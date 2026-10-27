module

public import CFSG.LocalAnalysis.StandardType.GGE6ThreeCompanion1625Contracts

public section

namespace CFSG.StandardType.S2MathAs1E6Companion1625

open CFSG CFSG.Assembly CFSG.StandardType
open CFSG.StandardType.GGK0MarkedKacIface1587
open CFSG.StandardType.E6Centralizer1585
open CFSG.HardMathSupport.Timmesfeld.LangTorus
open CFSG.LieType.AlgebraicGroups
open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

@[expose] def B1aOn (Omega : Type) [Field Omega] [IsAlgClosed Omega] [CharP Omega 2] :
    Prop :=
  ∀ (lab : LargeEvenLabel) (R : Type) [Group R] (I : Set (MulAut R)) (phi : MulAut R)
    (ρ : MarkedRationalKacRealization Omega lab 3 R I phi)
    (j : Fin ρ.row.D.orbits.length),
    LargeEvenInLambda2 lab → (∀ k, k = j) → ρ.row.D.orbits[j].qs = true →
    centralizerGroup ρ =
      ((geomCentralizer ρ ⊓ ρ.setup.D.model).subgroupOf ρ.setup.D.model).map ρ.modelAction ∧
    B1BruhatAt ρ j

@[expose] def B1bOn (Omega : Type) [Field Omega] [IsAlgClosed Omega] [CharP Omega 2] :
    Prop :=
  ∀ (lab : LargeEvenLabel) (R : Type) [Group R] (I : Set (MulAut R)) (phi : MulAut R)
    (ρ : MarkedRationalKacRealization Omega lab 3 R I phi)
    (j : Fin ρ.row.D.orbits.length),
    LargeEvenInLambda2 lab → (∀ k, k = j) → ρ.row.D.orbits[j].qs = true →
    connectedCentralizer ρ ≤ geomCentralizer ρ ∧
    ((connectedCentralizer ρ).subgroupOf (geomCentralizer ρ)).Normal ∧
    conn ρ ≤ centralizerGroup ρ ∧ innerComponent ρ j ≤ conn ρ ∧
    ((conn ρ).subgroupOf (centralizerGroup ρ)).Normal ∧
    ∀ u ∈ centralizerGroup ρ, ∀ x : R, x ∈ component ρ j ↔ u x ∈ component ρ j

@[expose] def B1GeomOn (Omega : Type) [Field Omega] [IsAlgClosed Omega] [CharP Omega 2]
    (row : LargeEvenLabel → LargeEvenLabel → Prop) (g : ℕ) : Prop :=
  ∀ (lab : LargeEvenLabel) (R : Type) [Group R] (I : Set (MulAut R)) (phi : MulAut R)
    (ρ : MarkedRationalKacRealization Omega lab 3 R I phi)
    (j : Fin ρ.row.D.orbits.length),
    LargeEvenInLambda2 lab → (∀ k, k = j) → ρ.row.D.orbits[j].qs = true →
    row lab ρ.row.D.orbits[j].lab →
    (connectedCentralizer ρ).relIndex (geomCentralizer ρ) = g

@[expose] def B1RatOn (Omega : Type) [Field Omega] [IsAlgClosed Omega] [CharP Omega 2]
    (row : LargeEvenLabel → LargeEvenLabel → Prop) (r : ℕ) : Prop :=
  ∀ (lab : LargeEvenLabel) (R : Type) [Group R] (I : Set (MulAut R)) (phi : MulAut R)
    (ρ : MarkedRationalKacRealization Omega lab 3 R I phi)
    (j : Fin ρ.row.D.orbits.length),
    LargeEvenInLambda2 lab → (∀ k, k = j) → ρ.row.D.orbits[j].qs = true →
    row lab ρ.row.D.orbits[j].lab →
    (conn ρ).relIndex (centralizerGroup ρ) = r

theorem b1On_of_pieces {Omega : Type} [Field Omega] [IsAlgClosed Omega] [CharP Omega 2]
    {row : LargeEvenLabel → LargeEvenLabel → Prop} {g r : ℕ}
    (ha : B1aOn Omega) (hb : B1bOn Omega) (hg : B1GeomOn Omega row g)
    (hr : B1RatOn Omega row r) : B1On Omega row g r := by
  intro lab R _ I phi ρ j hΛ hj hqs hrow
  obtain ⟨hC, hBr⟩ := ha lab R I phi ρ j hΛ hj hqs
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hb lab R I phi ρ j hΛ hj hqs
  exact ⟨⟨hC, h1, h2, hg lab R I phi ρ j hΛ hj hqs hrow, h3, h4, h5,
    hr lab R I phi ρ j hΛ hj hqs hrow, h6⟩, hBr⟩

@[expose] def B2SatQ2On (Omega : Type) [Field Omega] [IsAlgClosed Omega] [CharP Omega 2]
    (row : LargeEvenLabel → LargeEvenLabel → Prop) : Prop :=
  ∀ (lab : LargeEvenLabel) (R : Type) [Group R] (I : Set (MulAut R)) (phi : MulAut R)
    (ρ : MarkedRationalKacRealization Omega lab 3 R I phi)
    (j : Fin ρ.row.D.orbits.length),
    LargeEvenInLambda2 lab → (∀ k, k = j) → ρ.row.D.orbits[j].qs = true →
    row lab ρ.row.D.orbits[j].lab → lab.n = 1 →
    ∀ z ∈ connectedCentralizer ρ, z ∈ ρ.setup.D.model →
      (∀ x ∈ component ρ j, Commute z (ρ.iota x)) → ∀ y ∈ kernelSpan ρ, Commute z y

end CFSG.StandardType.S2MathAs1E6Companion1625

end
