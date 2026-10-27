module

public import Certificates.Data.Kernel.Misc.ArrEnum

public section

namespace CFSG.KC.Q8Wit

open CFSG.KC.Enum (pcomp pidn)
open CFSG.KS (mask pinvS)
open CFSG.KC.LQT.P (allN anyN)

@[expose] noncomputable def q8EltK (n w x y s j : Nat) : Nat :=
  bif Nat.beq j 0 then pidn n w else
  bif Nat.beq j 1 then x else
  bif Nat.beq j 2 then s else
  bif Nat.beq j 3 then pcomp n w (mask w) s x else
  bif Nat.beq j 4 then y else
  bif Nat.beq j 5 then pcomp n w (mask w) y x else
  bif Nat.beq j 6 then pcomp n w (mask w) y s else
  pcomp n w (mask w) y (pcomp n w (mask w) s x)

@[expose] noncomputable def commK (n w a b : Nat) : Bool :=
  Nat.beq (pcomp n w (mask w) a b) (pcomp n w (mask w) b a)

@[expose] noncomputable def outsideK (n w x y s c a : Nat) : Bool :=
  allN 8 fun j => !Nat.beq (pcomp n w (mask w) c a) (pcomp n w (mask w) (q8EltK n w x y s j) c)

@[expose] noncomputable def wit4K (n w x y s c ci : Nat) : Bool :=
  commK n w c s && (outsideK n w x y s c x || outsideK n w x y s c y) &&
    (!commK n w x (pcomp n w (mask w) (pcomp n w (mask w) c x) ci) ||
      !commK n w x (pcomp n w (mask w) (pcomp n w (mask w) c y) ci) ||
      !commK n w y (pcomp n w (mask w) (pcomp n w (mask w) c x) ci) ||
      !commK n w y (pcomp n w (mask w) (pcomp n w (mask w) c y) ci))

@[expose] noncomputable def wit5K (n w x y s g gi : Nat) : Bool :=
  anyN 8 fun j =>
    (!commK n w (q8EltK n w x y s j) x || !commK n w (q8EltK n w x y s j) y) &&
      commK n w (pcomp n w (mask w) (pcomp n w (mask w) g (q8EltK n w x y s j)) gi) s &&
      (outsideK n w x y s (pcomp n w (mask w) (pcomp n w (mask w) g (q8EltK n w x y s j)) gi) x ||
        outsideK n w x y s (pcomp n w (mask w) (pcomp n w (mask w) g (q8EltK n w x y s j)) gi) y)

@[expose] noncomputable def q8WitFreeK (n w N : Nat) (T SQ I : Nat → Nat) (nc : Nat)
    (C CI : Nat → Nat) : Bool :=
  allN N fun i =>
    Nat.beq (SQ i) (pidn n w) || !Nat.beq (pcomp n w (mask w) (SQ i) (SQ i)) (pidn n w) ||
      allN N fun j =>
        !Nat.beq (SQ j) (SQ i) ||
          !Nat.beq (pcomp n w (mask w) (T j) (T i)) (pcomp n w (mask w) (I i) (T j)) ||
          anyN nc fun k => wit4K n w (T i) (T j) (SQ i) (C k) (CI k) ||
            wit5K n w (T i) (T j) (SQ i) (C k) (CI k)

@[expose] noncomputable def tabsK (n w N : Nat) (T SQ I : Nat → Nat) : Bool :=
  allN N fun i => Nat.beq (SQ i) (pcomp n w (mask w) (T i) (T i)) &&
    Nat.beq (I i) (pinvS n w (mask w) (T i))

@[expose] noncomputable def invsK (n w nc : Nat) (C CI : Nat → Nat) : Bool :=
  allN nc fun k => Nat.beq (CI k) (pinvS n w (mask w) (C k))

end CFSG.KC.Q8Wit

end
