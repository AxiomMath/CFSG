module

public import Certificates.Data.Kernel.L5.Sh0Gam
public import Certificates.Data.Kernel.L5.Sh2Mul

public section

namespace CFSG.KD.L5.E16

open CFSG.Certificates.Kernel.L5S CFSG.Certificates.Kernel.PkCV CFSG.KD.L5
  CFSG.GH74.GLS.C3.Layer2.L5

@[expose] def mulT (t g : Nat → Nat) (s : Nat) (p q : Nat × Bool) : Nat × Bool :=
  match p.2, q.2 with
  | false, false => (t (p.1 * 128 + q.1), false)
  | false, true => (t (p.1 * 128 + q.1), true)
  | true, false => (t (p.1 * 128 + g q.1), true)
  | true, true => (t (t (p.1 * 128 + g q.1) * 128 + s), false)

@[expose] def invT (t iv g : Nat → Nat) (s : Nat) (p : Nat × Bool) : Nat × Bool :=
  match p.2 with
  | false => (iv p.1, false)
  | true => (t (iv s * 128 + g (iv p.1)), true)

@[expose] def eltsT : List (Nat × Bool) :=
  (List.range 128).flatMap fun i => [(i, false), (i, true)]

@[expose] def invsT (mul : Nat × Bool → Nat × Bool → Nat × Bool) : List (Nat × Bool) :=
  eltsT.filter fun p => decide (mul p p = (0, false))

@[expose] def centT (mul : Nat × Bool → Nat × Bool → Nat × Bool) (I : List (Nat × Bool))
    (p : Nat × Bool) : Nat :=
  (I.filter fun q => decide (mul p q = mul q p)).length

@[expose] def e1T (mul : Nat × Bool → Nat × Bool → Nat × Bool) : Bool :=
  (invsT mul).all fun p => !p.2 || decide (centT mul (invsT mul) p < 16)

@[expose] def invs0T (mul : Nat × Bool → Nat × Bool → Nat × Bool) : List (Nat × Bool) :=
  (invsT mul).filter fun q => !q.2

@[expose] def e2T (mul : Nat × Bool → Nat × Bool → Nat × Bool) (A : List Nat) : Bool :=
  (invs0T mul).all fun p => decide (p.1 ∈ A) || decide (centT mul (invs0T mul) p < 16)

@[expose] def conjsT (mul : Nat × Bool → Nat × Bool → Nat × Bool) (inv : Nat × Bool → Nat × Bool)
    (R : List Nat) (i : Nat) : List (Nat × Bool) :=
  R.map fun r => mul (mul (i, true) (r, false)) (inv (i, true))

@[expose] def mvT (mul : Nat × Bool → Nat × Bool → Nat × Bool) (inv : Nat × Bool → Nat × Bool)
    (R R₁ : List Nat) : Bool :=
  (List.range 128).all fun i => R₁.all fun j =>
    (conjsT mul inv R i).any fun c => decide (c = (j, false))

@[expose] def gT (m j : Nat) : Nat := if j < 128 then gamN m j else 0

@[expose] noncomputable def mulK (m : Nat) : Nat × Bool → Nat × Bool → Nat × Bool :=
  mulT tF (gT m) (ssK.getD m 0)

@[expose] noncomputable def invK (m : Nat) : Nat × Bool → Nat × Bool :=
  invT tF iT (gT m) (ssK.getD m 0)

@[expose] def rK : List Nat := [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80, 88, 96, 104, 112, 120]

@[expose] def r1K : List Nat := [0, 3, 4, 7, 32, 35, 36, 39, 64, 67, 68, 71, 96, 99, 100, 103]

@[expose] noncomputable def R1IdxC : List Nat :=
  (List.range 128).filter fun i => decide (sh0C.getD i 1 ∈ R1L.map cOf)

@[expose] noncomputable def tabsE16 : Bool :=
  decide (RIdxC = rK) && decide (R1IdxC = r1K) &&
    (List.range 4).all fun m => decide (gamL m = (List.range 128).map (gamN m))

@[expose] noncomputable def ch5068 (m : Nat) : Bool :=
  e1T (mulK m) && e2T (mulK m) (rK ++ r1K) && mvT (mulK m) (invK m) rK r1K

end CFSG.KD.L5.E16

end
