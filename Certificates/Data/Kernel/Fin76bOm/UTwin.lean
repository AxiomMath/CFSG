module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.UTableSpec
public import Mathlib.GroupTheory.SpecificGroups.Dihedral

public section

namespace CFSG.KC.Fin76bU

open CFSG.EvenSporadicStandard.Fin76b

@[expose] def fldU (w x i : Nat) : Nat := (x >>> (w * i)) % 2 ^ w

@[expose] def mU (P a b : Nat) : Nat := fldU 5 P (32 * a + b)

@[expose] def phU (x a : Nat) : Nat × Nat := (fldU 8 x a / 32, fldU 8 x a % 32)

@[expose] def peqU (m : Nat → Nat → Nat) (tI : Nat) (x y : Nat × Nat) : Bool :=
  (x.1 == y.1 && x.2 == y.2) || (y.1 == dMul x.1 2 && y.2 == m x.2 tI)

@[expose] def verU (m : Nat → Nat → Nat) (tI : Nat) (u : Nat × Nat) (x : Nat) : Bool :=
  ((List.range 32).all fun a => (List.range 32).all fun b =>
    peqU m tI (phU x (m a b)) (dMul (phU x a).1 (phU x b).1, m (phU x a).2 (phU x b).2)) &&
  ((List.range 32).all fun a => (List.range 32).all fun b =>
    a == b || !peqU m tI (phU x a) (phU x b)) &&
  ((List.range 32).all fun a =>
    peqU m tI (dMul (phU x a).1 u.1, m (phU x a).2 u.2) (dMul u.1 (phU x a).1, m u.2 (phU x a).2)) &&
  ((List.range 32).all fun a => !peqU m tI (phU x a) u)

@[expose] def condU (m : Nat → Nat → Nat) (tI i k : Nat) : Bool :=
  peqU m tI (dMul i i, m k k) (0, 0) && !peqU m tI (i, k) (0, 0) && !peqU m tI (i, k) (0, tI)

@[expose] noncomputable def allU (m : Nat → Nat → Nat) (tI : Nat) (ws : List Nat) : Nat → Bool :=
  List.rec (motive := fun _ => Nat → Bool) (fun _ => true)
    (fun x _ ih p => (!condU m tI (p / 32) (p % 32) || verU m tI (p / 32, p % 32) x) && ih (p + 1))
    ws

@[expose] def globU (m : Nat → Nat → Nat) (tI : Nat) : Bool :=
  decide (tI < 32) && tI != 0 && m tI tI == 0 &&
    (List.range 32).all fun a =>
      !((List.range 32).all fun b => m a b == m b a) || a == 0 || a == tI

@[expose] noncomputable def uChkU (P tI : Nat) (WS : List Nat) : Bool :=
  globU (mU P) tI && WS.length == 256 && allU (mU P) tI WS 0

end CFSG.KC.Fin76bU

end
