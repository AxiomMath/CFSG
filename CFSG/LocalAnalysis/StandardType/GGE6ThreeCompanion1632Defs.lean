module

public import CFSG.LocalAnalysis.StandardType.GGE6ThreeCompanion1625Pieces

public section

namespace CFSG.StandardType.S2MathAs1E6Companion1625

open CFSG CFSG.Assembly CFSG.StandardType
open CFSG.StandardType.GGK0MarkedKacIface1587
open CFSG.StandardType.E6Centralizer1585
open CFSG.HardMathSupport.Timmesfeld.LangTorus
open CFSG.LieType.AlgebraicGroups
open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

@[expose] def WeylIndexAt {Omega : Type} [Field Omega] [IsAlgClosed Omega] [CharP Omega 2]
    {lab : LargeEvenLabel} {p : ℕ} {R : Type} [Group R] {I : Set (MulAut R)} {phi : MulAut R}
    (ρ : MarkedRationalKacRealization Omega lab p R I phi) : Prop :=
  (connectedCentralizer ρ).relIndex (geomCentralizer ρ) =
    (kernelReflectionGroup ρ.a).relIndex (rootCharStabilizerSubgroup ρ.a)

@[expose] def GeomIndexByDatumAt {Omega : Type} [Field Omega] [IsAlgClosed Omega] [CharP Omega 2]
    {lab : LargeEvenLabel} {p : ℕ} {R : Type} [Group R] {I : Set (MulAut R)} {phi : MulAut R}
    (ρ : MarkedRationalKacRealization Omega lab p R I phi) : Prop :=
  (connectedCentralizer ρ).relIndex (geomCentralizer ρ) = ρ.row.D.stabΩ

@[expose] def WeylIndexByDatumAt {Omega : Type} [Field Omega] [IsAlgClosed Omega] [CharP Omega 2]
    {lab : LargeEvenLabel} {p : ℕ} {R : Type} [Group R] {I : Set (MulAut R)} {phi : MulAut R}
    (ρ : MarkedRationalKacRealization Omega lab p R I phi) : Prop :=
  (kernelReflectionGroup ρ.a).relIndex (rootCharStabilizerSubgroup ρ.a) = ρ.row.D.stabΩ

@[expose] def LangOnConnectedAt {Omega : Type} [Field Omega] [IsAlgClosed Omega] [CharP Omega 2]
    {lab : LargeEvenLabel} {p : ℕ} {R : Type} [Group R] {I : Set (MulAut R)} {phi : MulAut R}
    (ρ : MarkedRationalKacRealization Omega lab p R I phi) : Prop :=
  ∀ h ∈ connectedCentralizer ρ, ∃ z ∈ connectedCentralizer ρ, ρ.setup.D.step z = z * h

@[expose] def FixedCosetRepresentativeAt {Omega : Type} [Field Omega] [IsAlgClosed Omega]
    [CharP Omega 2]
    {lab : LargeEvenLabel} {p : ℕ} {R : Type} [Group R] {I : Set (MulAut R)} {phi : MulAut R}
    (ρ : MarkedRationalKacRealization Omega lab p R I phi) : Prop :=
  ∀ x ∈ geomCentralizer ρ, ρ.setup.D.step x * x⁻¹ ∈ connectedCentralizer ρ →
    ∃ y ∈ geomCentralizer ρ, y ∈ ρ.setup.D.model ∧ y * x⁻¹ ∈ connectedCentralizer ρ

@[expose] def FrobeniusTrivialAt {Omega : Type} [Field Omega] [IsAlgClosed Omega] [CharP Omega 2]
    {lab : LargeEvenLabel} {p : ℕ} {R : Type} [Group R] {I : Set (MulAut R)} {phi : MulAut R}
    (ρ : MarkedRationalKacRealization Omega lab p R I phi) : Prop :=
  ∀ x ∈ geomCentralizer ρ, ρ.setup.D.step x * x⁻¹ ∈ connectedCentralizer ρ

@[expose] def RootActionAgreeAt {Omega : Type} [Field Omega] [IsAlgClosed Omega] [CharP Omega 2]
    {lab : LargeEvenLabel} {p : ℕ} {R : Type} [Group R] {I : Set (MulAut R)} {phi : MulAut R}
    (ρ : MarkedRationalKacRealization Omega lab p R I phi) : Prop :=
  ∀ v : Fin ρ.tau.rank → ℤ, ρ.setup.ρ v = ρ.frobLinear v

@[expose] def WeylStepAt {Omega : Type} [Field Omega] [IsAlgClosed Omega] [CharP Omega 2]
    {lab : LargeEvenLabel} {p : ℕ} {R : Type} [Group R] {I : Set (MulAut R)} {phi : MulAut R}
    (ρ : MarkedRationalKacRealization Omega lab p R I phi) : Prop :=
  ∃ t : WeylGroup ρ.tau,
    (∀ v : Fin ρ.tau.rank → ℤ,
      t • v = (if ρ.row.tw then (-1 : ℤ) else 1) • ρ.frobLinear v) ∧
    (∀ w : WeylGroup ρ.tau,
      ρ.setup.D.step (canonicalRep (coxeterSystem ρ.tau) Omega w) =
        canonicalRep (coxeterSystem ρ.tau) Omega (t * w * t⁻¹))

@[expose] def LangOnConnectedOn (Omega : Type) [Field Omega] [IsAlgClosed Omega] [CharP Omega 2]
    (row : LargeEvenLabel → LargeEvenLabel → Prop) : Prop :=
  ∀ (lab : LargeEvenLabel) (R : Type) [Group R] (I : Set (MulAut R)) (phi : MulAut R)
    (ρ : MarkedRationalKacRealization Omega lab 3 R I phi)
    (j : Fin ρ.row.D.orbits.length),
    LargeEvenInLambda2 lab → (∀ k, k = j) → ρ.row.D.orbits[j].qs = true →
    row lab ρ.row.D.orbits[j].lab →
    LangOnConnectedAt ρ

@[expose] def FrobeniusTrivialOn (Omega : Type) [Field Omega] [IsAlgClosed Omega] [CharP Omega 2]
    (row : LargeEvenLabel → LargeEvenLabel → Prop) : Prop :=
  ∀ (lab : LargeEvenLabel) (R : Type) [Group R] (I : Set (MulAut R)) (phi : MulAut R)
    (ρ : MarkedRationalKacRealization Omega lab 3 R I phi)
    (j : Fin ρ.row.D.orbits.length),
    LargeEvenInLambda2 lab → (∀ k, k = j) → ρ.row.D.orbits[j].qs = true →
    row lab ρ.row.D.orbits[j].lab →
    FrobeniusTrivialAt ρ

end CFSG.StandardType.S2MathAs1E6Companion1625

end
