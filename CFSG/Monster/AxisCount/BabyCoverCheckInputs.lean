module

public import CFSG.Certificates.Kernel.AxisPlane.Orbit
public import CFSG.Monster.AxisCount.BabyBasic
public import Mathlib.Data.Set.Card

public section

namespace CFSG.Monster.AxisCount.Baby

open CFSG.Monster.AxisCount.Native

@[expose] def babyRows (o : BabyOrbit) : Array (Array ℕ) := (o.U.map Cover.wordRows).toArray

@[expose] def babyWordsOK (o : BabyOrbit) : Bool :=
  o.U.all (fun w => w.all Gen.isVis) && o.h.toList.all (fun w => w.all Gen.isVis) &&
    o.h.size == o.lam.size && o.lam.size == o.size.size &&
    (o.h.toList.zip o.lam.toList).all (fun x => Cover.l2Word x.1 x.2 == 63) &&
    o.size.toList.sum == 46575

@[expose] def BabyOrbits (o : BabyOrbit) : Prop :=
  babyWordsOK o = true ∧ ∀ r < o.lam.size,
    CFSG.KC.AxisPlane.natOrbit (babyRows o) o.lam[r]! ⊆ Set.Iio (2 ^ 24) ∧
    (CFSG.KC.AxisPlane.natOrbit (babyRows o) o.lam[r]!).ncard = o.size[r]! ∧
    ∀ r' < o.lam.size, r ≠ r' → Disjoint (CFSG.KC.AxisPlane.natOrbit (babyRows o) o.lam[r]!)
      (CFSG.KC.AxisPlane.natOrbit (babyRows o) o.lam[r']!)

end CFSG.Monster.AxisCount.Baby
