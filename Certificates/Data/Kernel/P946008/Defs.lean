module

public import Certificates.Data.ParrottExtraspecial

public section

namespace CFSG.KC.P946008

open CFSG.RankThree.GF2n.Parrott

@[expose] noncomputable def packT (f : Nat → Nat) (n : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) 0 (fun k acc => acc + f k % 256 * 256 ^ k) n

@[expose] def lk (T p : Nat) : Nat := T / 256 ^ p % 256

@[expose] noncomputable def allN (n : Nat) (f : Nat → Bool) : Bool :=
  Nat.rec (motive := fun _ => Bool) true (fun k r => f k && r) n

@[expose] def phiK (T C p : Nat) : Nat :=
  lk T (p % 256) ||| ((((p >>> 8) % 2) ^^^ lk C (p % 256)) <<< 8)

@[expose] noncomputable def cocyRow (T C p a c : Nat) : Bool :=
  allN 256 fun q => lk C (p ^^^ q) ^^^ c ^^^ lk C q == bhMask a (lk T q) ^^^ bhMask p q

@[expose] noncomputable def cocyK (T C : Nat) : Bool :=
  allN 256 fun p => cocyRow T C p (lk T p) (lk C p)

@[expose] noncomputable def cubeK (T C : Nat) : Bool :=
  allN 512 fun p => phiK T C (phiK T C (phiK T C p)) == p

@[expose] def fixG (φ : Nat → Nat) : List Nat := (List.range 512).filter (fun p => φ p == p)

@[expose] def noncommG (φ : Nat → Nat) : Bool :=
  let F := fixG φ
  F.any fun p => F.any fun q => mulMask p q != mulMask q p

@[expose] def centralG (φ : Nat → Nat) : Bool := (fixG φ).all fun p => p % 256 == 0

@[expose] def invCountG (φ : Nat → Nat) : Nat := ((fixG φ).filter fun p => mulMask p p == 0).length

@[expose] def centreG (φ : Nat → Nat) : Nat :=
  let F := fixG φ
  (F.filter fun z => F.all fun q => mulMask z q == mulMask q z).length

@[expose] def ord4G (φ : Nat → Nat) : Bool :=
  (fixG φ).all fun p => mulMask p (mulMask p (mulMask p p)) == 0

@[expose] noncomputable def liftK (T C fixedCard invCard : Nat) (noncommValue : Bool) : Bool :=
  (phiK T C 0 == 0) &&
  ((List.range 512).filter (fun p => phiK T C p == p)).length == fixedCard &&
  (noncommG (phiK T C) == noncommValue) &&
  ((List.range 512).filter (fun p => phiK T C p == p ∧ mulMask p p == 0)).length == invCard &&
  cubeK T C && cocyK T C

end CFSG.KC.P946008
