
module

public import CFSG.Quasithin.Background.A3StructureDefs

@[expose] public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Quasithin.A36B

open CFSG.SectionRank CFSG.SectionRank.Ccomm CFSG.Open

structure PrimeData (X : Type) [Group X] (q : ℕ) where
  P : Subgroup ↥(CFSG.pCore q X)
  K : Subgroup X
  normal_K : K.Normal
  ne_top : K ≠ ⊤
  supercritical : IsSupercritical q P
  faithful : ∀ α : MulAut ↥(CFSG.pCore q X), (orderOf α).Coprime q →
    (∀ x ∈ P, x⁻¹ * α x ∈ frattiniIn P) → α = 1
  iso : IsElemAbelianOfRank q 2 ↥P ∨ IsPOnePlusTwo q ↥P
  mem_K : ∀ x : X, x ∈ K ↔ ∀ d ∈ P, d⁻¹ * MulAut.conjNormal x d ∈ frattiniIn P
  sl2 : IsSL2 q (X ⧸ K) ∨ ((q % 5 = 1 ∨ q % 5 = 4) ∧ IsSL2 5 (X ⧸ K))
  card_W : Nat.card (↥P ⧸ frattini ↥P) = q ^ 2
  inv_W : ∀ t : X, t ∉ K → t ^ 2 ∈ K → ∀ d ∈ P, d * MulAut.conjNormal t d ∈ frattiniIn P
  irr : frattini ↥P = ⊥ → ∀ U : Subgroup ↥(CFSG.pCore q X), U ≤ P →
    (∀ h : X, ∀ u ∈ U, MulAut.conjNormal h u ∈ U) → U = ⊥ ∨ U = P

attribute [instance] PrimeData.normal_K

variable {X : Type} [Group X]

end CFSG.Quasithin.A36B
