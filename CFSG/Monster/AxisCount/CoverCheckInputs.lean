module

public import CFSG.Monster.AxisCount.CertData
public import CFSG.Certificates.Kernel.AxisPlane.Orbit
public import Mathlib.Data.Set.Card

public section

namespace CFSG.Monster.AxisCount.Cert

@[expose] def wordsOK (i : Fin 12) : Bool :=
  (UA i).all Native.Gen.isVis && (UB i).all Native.Gen.isVis &&
    (List.range (nW i)).all fun r =>
      (hW i r).all Native.Gen.isVis && Native.Cover.l2Word (hW i r) (lamW i r) == 63

@[expose] def rowsW (i : Fin 12) : Array (Array ℕ) :=
  #[Native.Cover.wordRows (UA i), Native.Cover.wordRows (UB i)]

@[expose] def CoverOrbits (i : Fin 12) : Prop :=
  wordsOK i = true ∧ ∀ r < nW i,
    CFSG.KC.AxisPlane.natOrbit (rowsW i) (lamW i r) ⊆ Set.Iio (2 ^ 24) ∧
    (CFSG.KC.AxisPlane.natOrbit (rowsW i) (lamW i r)).ncard = sizeW i r ∧
    ∀ r' < nW i, r ≠ r' → Disjoint (CFSG.KC.AxisPlane.natOrbit (rowsW i) (lamW i r))
      (CFSG.KC.AxisPlane.natOrbit (rowsW i) (lamW i r'))

end CFSG.Monster.AxisCount.Cert
