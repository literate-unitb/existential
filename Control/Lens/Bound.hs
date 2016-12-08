{-# LANGUAGE TypeOperators
    ,ConstraintKinds
    ,PolyKinds #-}
module Control.Lens.Bound where

import Control.Category
import Control.Lens
import Control.Monad
import Data.Constraint
import Data.Monoid hiding (All)
import Data.Proxy
import Data.Void

import Prelude hiding ((.),id)

class All (a :: k) where 
instance All a

type BoundLensType c0a c0b c1a c1b f s t a b = forall i.
            ( forall x. (c0a i,c0b) :- (c1a x,c1b) 
                -> Prism' x i
                -> a x -> f (b x) )
            -> s i -> f (t i)

newtype BFocus p r c0 c1 f a b = BFocus
            { _unfocus :: forall x.
                    p :- (c0 x,c1)
                ->  Prism' x r
                ->  a x -> f (b x) }

type BoundLens c0a c0b c1a c1b s t a b = forall f p r. (Functor f) =>
            BoundLensLike p r f c0a c0b c1a c1b s t a b

type BoundLens' c0 c1 s a = BoundLens c0 c1 c0 c1 s s a a

type BoundTraversal c0a c0b c1a c1b s t a b = forall f p q. (Applicative f) =>
            BoundLensLike p q f c0a c0b c1a c1b s t a b

type BoundGetting p q c0 c1 r s a = BoundLensLike p q (Const r) c0 c1 c0 c1 s s a a

type BoundFold c0 c1 s a = forall m p q. Monoid m => 
            BoundGetting p q c0 c1 m s a

type BoundTraversal' c0 c1 s a = BoundTraversal c0 c1 c0 c1 s s a a

type BoundLensLike p r f c0a c0b c1a c1b s t a b =
               BFocus p r c1a c1b f a b 
            -> BFocus p r c0a c0b f s t

type BoundLensLike' p q f c0 c1 s a = BoundLensLike p q f c0 c1 c0 c1 s s a a

type ExLensLike f c0a c0b s t a b =
               BFocus () Void c0a c0b f a b 
            -> s -> f t

type ExLensType c0a c0b f s t a b = 
            ( forall x. (c0a x,c0b) 
                => a x 
                -> f (b x) )
            -> s -> f t

type ExLens c0a c0b s t a b = forall f. Functor f 
            => ExLensLike f c0a c0b s t a b

type ExTraversal c0a c0b s t a b = forall f. Applicative f 
            => ExLensLike f c0a c0b s t a b

type ExLens' c0a c0b s a = ExLens c0a c0b s s a a

type ExTraversal' c0a c0b s a = ExTraversal c0a c0b s s a a

instance Monoid m => Monoid (BFocus p r c0 c1 (Const m) a b) where
    mempty = BFocus $ \_c _p _x -> Const mempty
    BFocus f `mappend` BFocus g = BFocus $ \c p -> f c p `mappend` g c p

instance Monad m => Category (BFocus p r c0 c1 m) where
    id = BFocus $ \_ _ -> pure
    BFocus f . BFocus g = BFocus $ \c p -> f c p <=< g c p

makeBLens :: BoundLensType c0a c0b c1a c1b f s t a b
          -> BoundLensLike p q f c0a c0b c1a c1b s t a b
makeBLens f g = BFocus $ \x pr -> f $ \p pr' -> _unfocus g (p.x) (pr'.pr)

makeBLens' :: (forall i.
                ( forall x. 
                       Prism' x i
                    -> a x -> f (b x) )
                -> s i -> f (t i))
           -> BoundLensLike p q f c0a c0b All c0b s t a b
makeBLens' f = makeBLens $ \g -> f $ g $ Sub Dict *** id

applyBLens :: (forall p q. BoundLensLike p q f c0a c0b c1a c1b s t a b)
           -> BoundLensType c0a c0b c1a c1b f s t a b
applyBLens f g = _unfocus (f $ BFocus g) id id

makeExLens :: (Proxy c0b -> ExLensType c0a c0b f s t a b)
           -> ExLensLike f c0a c0b s t a b
makeExLens f (BFocus g) = f Proxy $ g (Sub Dict) (prism' absurd $ const Nothing)

applyExLens :: ExLensLike f c0a c0b s t a b
            -> ExLensType c0a c0b f s t a b
applyExLens f g = f (BFocus $ \(Sub Dict) _ -> g)

overExLens :: ExLensLike Identity c0a c0b s t a b
           -> (forall x. (c0a x, c0b)
                  => a x -> b x)
           -> s -> t
overExLens f g = runIdentity . applyExLens f (Identity . g)

viewExLens :: ExLensLike (Const r) c0a c0b s t a b
           -> (forall x. (c0a x, c0b)
                  => a x -> r)
           -> s -> r
viewExLens f g = getConst . applyExLens f (Const . g)

applyRaw :: (forall p q. BoundLensLike p q f c0a c0b c1a c1b s t a b)
         -> (forall x.
                a x -> f (b x))
         -> s i -> f (t i)
applyRaw ln f = applyRawWith ln $ \_ -> f

applyRawWith :: (forall p q. BoundLensLike p q f c0a c0b c1a c1b s t a b)
             -> (forall x. Prism' x i
                    -> a x -> f (b x))
             -> s i -> f (t i)
applyRawWith ln f = applyBLens ln $ \_ -> f

applyAsms :: (c0a i,c0b)
          => (forall p q. BoundLensLike p q f c0a c0b c1a c1b s t a b)
          -> (forall x. (c1a x,c1b)
                => a x -> f (b x))
          -> s i -> f (t i)
applyAsms ln f = applyAsmsWith ln $ \_ -> f

applyAsmsWith :: (c0a i,c0b)
              => (forall p q. BoundLensLike p q f c0a c0b c1a c1b s t a b)
              -> (forall x. (c1a x,c1b)
                    => Prism' x i
                    -> a x -> f (b x))
              -> s i -> f (t i)
applyAsmsWith ln f = applyBLens ln $ \(Sub Dict) -> f

applyAsmA :: (c0a i,c0b)
          => (forall p q. BoundLensLike p q f c0a c0b c1a c1b s t a b)
          -> (forall x. (c1a x,c1b)
                => a x -> f (b x))
          -> s i -> f (t i)
applyAsmA ln f = applyAsmAWith ln $ \_ -> f

applyAsmB :: (c0a i,c0b)
          => (forall p q. BoundLensLike p q f c0a c0b c1a c1b s t a b)
          -> (forall x. (c1a x,c1b)
                => a x -> f (b x))
          -> s i -> f (t i)
applyAsmB ln f = applyAsmBWith ln $ \_ -> f

applyAsmAWith :: (c0a i,c0b)
              => (forall p q. BoundLensLike p q f c0a c0b c1a c1b s t a b)
              -> (forall x. (c1a x,c1b)
                    => Prism' x i
                    -> a x -> f (b x))
              -> s i -> f (t i)
applyAsmAWith ln f = applyBLens ln $ \(Sub Dict) -> f

applyAsmAWith' :: (c0a i,c0b)
               => (forall p q. BoundLensLike p q f c0a c0b c1a c1b s t a b)
               -> (forall x. (c1a x,c1b)
                     => Fold x i
                     -> a x -> f (b x))
               -> s i -> f (t i)
applyAsmAWith' ln f = applyAsmAWith ln $ \pr -> f (withPrism pr $ \_ -> folding)

applyAsmBWith :: (c0a i,c0b)
              => (forall p q. BoundLensLike p q f c0a c0b c1a c1b s t a b)
              -> (forall x. (c1a x,c1b)
                    => Prism' x i
                    -> a x -> f (b x))
              -> s i -> f (t i)
applyAsmBWith ln f = applyBLens ln $ \(Sub Dict) -> f

overRaw :: (forall p q. BoundLensLike p q Identity c0a c0b c1a c1b s t a b)
         -> (forall x.
                a x -> b x)
         -> s i -> t i
overRaw ln f = overRawWith ln $ \_ -> f

overRawWith :: (forall p q. BoundLensLike p q Identity c0a c0b c1a c1b s t a b)
            -> (forall x. Prism' x i
                    -> a x -> b x)
            -> s i -> t i
overRawWith ln f = runIdentity . applyRawWith ln (\c p -> Identity $ f c p)

overAsms :: (c0a i,c0b)
          => (forall p q. BoundLensLike p q Identity c0a c0b c1a c1b s t a b)
          -> (forall x. (c1a x,c1b)
                => a x -> b x)
          -> s i -> t i
overAsms ln f = overAsmsWith ln $ \_ -> f

overAsmsWith :: (c0a i,c0b)
              => (forall p q. BoundLensLike p q Identity c0a c0b c1a c1b s t a b)
              -> (forall x. (c1a x,c1b)
                    => Prism' x i
                    -> a x -> b x)
              -> s i -> t i
overAsmsWith ln f = runIdentity . applyAsmsWith ln (\c p -> Identity $ f c p)

overAsmA :: (c0a i,c0b)
          => (forall p q. BoundLensLike p q Identity c0a c0b c1a c1b s t a b)
          -> (forall x. (c1a x,c1b)
                => a x -> b x)
          -> s i -> t i
overAsmA ln f = overAsmAWith ln $ \_ -> f

overAsmB :: (c0a i,c0b)
          => (forall p q. BoundLensLike p q Identity c0a c0b c1a c1b s t a b)
          -> (forall x. (c1a x,c1b)
                => a x -> b x)
          -> s i -> t i
overAsmB ln f = overAsmBWith ln $ \_ -> f

overAsmAWith :: (c0a i,c0b)
              => (forall p q. BoundLensLike p q Identity c0a c0b c1a c1b s t a b)
              -> (forall x. (c1a x,c1b)
                    => Prism' x i
                    -> a x -> b x)
              -> s i -> t i
overAsmAWith ln f = runIdentity . applyAsmAWith ln (\c p -> Identity $ f c p)

overAsmBWith :: (c0a i,c0b)
              => (forall p q. BoundLensLike p q Identity c0a c0b c1a c1b s t a b)
              -> (forall x. (c1a x,c1b)
                    => Prism' x i
                    -> a x -> b x)
              -> s i -> t i
overAsmBWith ln f = runIdentity . applyAsmBWith ln (\c p -> Identity $ f c p)

viewRaw :: (forall p q. BoundLensLike p q (Const r) c0a c0b c1a c1b s t a b)
         -> (forall x.
                a x -> r)
         -> s i -> r
viewRaw ln f = viewRawWith ln $ \_ -> f

viewRawWith :: (forall p q. BoundLensLike p q (Const r) c0a c0b c1a c1b s t a b)
            -> (forall x. Prism' x i
                    -> a x -> r)
            -> s i -> r
viewRawWith ln f = getConst . applyRawWith ln (\c p -> Const $ f c p)

viewAsms :: (c0a i,c0b)
         => (forall p q. BoundLensLike p q (Const r) c0a c0b c1a c1b s t a b)
         -> (forall x. (c1a x,c1b)
                => a x -> r)
         -> s i -> r
viewAsms ln f = viewAsmsWith ln $ \_ -> f

viewAsmsWith :: (c0a i,c0b)
              => (forall p q. BoundLensLike p q (Const r) c0a c0b c1a c1b s t a b)
              -> (forall x. (c1a x,c1b)
                    => Fold x i
                    -> a x -> r)
              -> s i -> r
viewAsmsWith ln f = getConst . applyAsmAWith' ln (\c p -> Const $ f c p)

viewAsmA :: (c0a i,c0b)
          => (forall p q. BoundLensLike p q (Const r) c0a c0b c1a c1b s t a b)
          -> (forall x. (c1a x,c1b)
                => a x -> r)
          -> s i -> r
viewAsmA ln f = viewAsmAWith ln $ \_ -> f

viewAsmAWith :: (c0a i,c0b)
              => (forall p q. BoundLensLike p q (Const r) c0a c0b c1a c1b s t a b)
              -> (forall x. (c1a x,c1b)
                    => Fold x i
                    -> a x -> r)
              -> s i -> r
viewAsmAWith ln f = getConst . applyAsmAWith' ln (\c p -> Const $ f c p)

mapConstrOnFocus :: c1' :- c1
                 -> BFocus p r c0 c1 f a b
                 -> BFocus p r c0 c1' f a b
mapConstrOnFocus d (BFocus f) = BFocus $ \p -> f ((id *** d).p)

mapConstr :: c1b :- c1b'
          -> c0b' :- c0b
          -> BoundLensLike p q f c0a c0b c1a c1b s t a b
          -> BoundLensLike p q f c0a c0b' c1a c1b' s t a b
mapConstr d0 d1 ln = mapConstrOnFocus d1 . ln . mapConstrOnFocus d0

fromEntail :: (forall i. (c0' i,c1') :- (c0 i,c1))
           -> BFocus p r c0 c1 f a b
           -> BFocus p r c0' c1' f a b
fromEntail d (BFocus f) = BFocus $ \x pr -> f (d.x) pr

fromLens :: (forall x. LensLike f (s x) (t x) (a x) (b x))
         -> BoundLensLike p q f c0a c0b c0a c0b s t a b
fromLens ln (BFocus f) = BFocus $ \x pr -> ln (f x pr)

preorder :: Monad f
         => BoundLensLike p q f c0a c0b c0a c0b a a a a
         -> BoundLensLike p q f c0a c0b c0a c0b a a a a
preorder ln f = f >>> (ln.preorder ln) f

postorder :: Monad f
          => BoundLensLike p q f c0a c0b c0a c0b a a a a
          -> BoundLensLike p q f c0a c0b c0a c0b a a a a
postorder ln f = (ln.preorder ln) f >>> f

preorderFold :: Monoid m
             => BoundLensLike p q (Const m) c0a c0b c0a c0b a a a a
             -> BoundLensLike p q (Const m) c0a c0b c0a c0b a a a a
preorderFold ln f = f <> (ln.preorderFold ln) f

postorderFold :: Monoid m
              => BoundLensLike p q (Const m) c0a c0b c0a c0b a a a a
              -> BoundLensLike p q (Const m) c0a c0b c0a c0b a a a a
postorderFold ln f = (ln.preorderFold ln) f <> f

toListOf :: (forall p q. BoundLensLike p q (Const (Endo [r])) c0a c0b c0a c0b s s a a)
         -> (forall x.
                a x -> r)
         -> s x -> [r]
toListOf ln f = ($ []) . appEndo . viewRaw ln (Endo . (++) . pure . f)

toListOf' :: (c0a x, c0b)
          => (forall p q. BoundLensLike p q (Const (Endo [r])) c0a c0b c0a c0b s s a a)
          -> (forall x.
                   (c0a x, c0b)
                => a x -> r)
          -> s x -> [r]
toListOf' ln f = ($ []) . appEndo . viewAsmA ln (Endo . (++) . pure . f)

-- toLens :: (forall p q. BoundLensLike p q f c0 c1 s t a b)
--        -> LensLike f (s x) (t x) (a x) (b x)
-- toLens ln f = unfocus (ln $ BFocus $ \p q pr -> mapping pr f) id id id













