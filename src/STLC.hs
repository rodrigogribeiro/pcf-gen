{-# LANGUAGE DeriveGeneric         #-}
{-# LANGUAGE DeriveDataTypeable    #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE TupleSections         #-}

module STLC where

import Unbound.Generics.LocallyNameless
import GHC.Generics
import Data.Typeable
import Test.QuickCheck
import Data.Functor.Identity
import Control.Monad.State
import Control.Monad.Except
import Control.Monad.Reader

-- definition of types and syntax

data Ty = TNat | Ty :-> Ty
          deriving (Eq, Show, Generic, Typeable)

data Term = Var (Name Term)
          | Lam (Bind (Name Term, Ty) Term)
          | App Term Term
          | Const Int
--          | LetRec (Bind (Rec (Name Term, Embed Term)) Term)
          deriving (Show, Generic, Typeable)

-- infrastructure for substitutions

instance Alpha Ty
instance Alpha Term

instance Subst Term Ty

instance Subst Term Term where
   isvar (Var x) = Just (SubstName x)
   isvar _       = Nothing


lam :: Name Term -> Ty -> Term -> Term
lam n t e = Lam (bind (n,t) e)

-- definition of the type checker

type Tc a = ExceptT String (ReaderT Ctx (FreshMT Identity)) a

runTc :: Tc a -> Either String a
runTc m
  = runIdentity $ runFreshMT $ flip runReaderT [] $ runExceptT m

withExtendedCtx :: Name Term -> Ty -> Tc a -> Tc a
withExtendedCtx n t m
  = local ((n, t) : ) m

lookupVar :: Name Term -> Tc Ty
lookupVar v
  = do
      ctx <- ask
      case lookup v ctx of
        Just t -> return t
        Nothing -> throwError "Variable not defined."

infer :: Term -> Tc Ty
infer (Const _)
  = return TNat
infer (Var v)
  = lookupVar v
infer (Lam b)
  = do
      ((n,t), e) <- unbind b
      t' <- withExtendedCtx n t (infer e)
      return (t :-> t')
infer (App e e')
  = do
      t <- infer e
      t' <- infer e'
      case t of
        (t1 :-> t2) | t' == t1 -> return t2
        _ -> throwError "Type error in application."


typeCorrect :: Term -> Ty -> Bool
typeCorrect e t
  = case runTc (infer e) of
      Left _ -> False
      Right t' -> t == t'


-- definition of the generator

type VarCounter = Int
type Depth = Int
type Ctx = [(Name Term, Ty)]

type LGen a = (ReaderT Ctx (StateT VarCounter Gen)) a

runLGen :: LGen a -> Gen a
runLGen m
  = fst <$> runStateT (runReaderT m []) 0

oneofM :: [LGen a] -> LGen a
oneofM [] = error "Cannot use on empty list"
oneofM gs
  = do
       v <- lift $ lift $ choose (0, length gs - 1)
       gs !! v

-- generate a variable

genNewVar :: LGen (Name Term)
genNewVar
  = do
      v <- lift $ get
      lift $ modify (1 +)
      return (string2Name $ "x_" ++ show v)

fromCtx :: Ty -> LGen [Term]
fromCtx ty
  = do
      ctx <- ask
      let f p = if snd p == ty then [Var $ fst p] else []
      return (concatMap f ctx)


withNewVar :: Ty -> LGen a -> LGen (Name Term, a)
withNewVar t m
  = do
       v <- genNewVar
       (v,) <$> local ((v, t) :) m

genType :: Depth -> LGen Ty
genType d
  | d <= 1    = pure TNat
  | otherwise
     = do
         let d2 = d `div` 2
         t <- oneofM [ pure TNat
                     , (:->) <$> genType d2 <*>
                                 genType d2
                     ]
         return t


instance Arbitrary Ty where
  arbitrary
    = do
         t <- choose (2,10)
         runLGen (genType t)


genConst :: LGen Term
genConst = lift $ lift $ Const <$> choose (1,100)

genNatTerm :: Depth -> LGen Term
genNatTerm d
  | d <= 1
    = do
        vs <- fromCtx TNat
        c  <- genConst
        lift $ lift $ elements (c : vs)
  | otherwise
    = genAppTerm d2 d2 TNat TNat
    where
      d2  = d `div` 2

genAppTerm :: Depth -> Depth -> Ty -> Ty -> LGen Term
genAppTerm d1 d2 dom ran
  = App <$> genTerm d1 (dom :-> ran) <*> genTerm d2 dom

genLamTerm :: Depth -> Ty -> Ty -> LGen Term
genLamTerm d dom ran
  | d <= 2 = let f (v, e) = lam v dom e
             in f <$> withNewVar dom (genTerm d ran)
  | otherwise = let f (v, e) = lam v dom e
                    d2 = d `div` 2
                in f <$> withNewVar dom (genTerm d ran)

genTerm :: Depth -> Ty -> LGen Term
genTerm d TNat
  = genNatTerm d 
genTerm d (t :-> t')
  | d <= 2    = genLamTerm d t t'
  | otherwise = genLamTerm d2 t t'
    where
      d2 = d `div` 2

gen :: Depth -> LGen Term
gen d
  = do
      t <- genType d
      genTerm 2 t

instance Arbitrary Term where
  arbitrary
    = do
         d <- choose (2,4)
         runLGen $ gen d


-- testing if the generator builds only type correct terms

generatorSound :: Property
generatorSound
  = forAll (arbitrary :: Gen Ty)
           (\ t -> forAll (runLGen $ genTerm 4 t)
                   (\ e -> typeCorrect e t == True))

testGenerator :: IO ()
testGenerator
  = quickCheckWith stdArgs {maxSuccess = 1000} generatorSound
