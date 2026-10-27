module

public import CFSG.LocalAnalysis.StandardType.GGOneFiveDefs

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

section Vocabulary

variable {G : Type} [Group G] [Finite G]

@[expose] def GGReflCentre {Bs : Subgroup G} (φ : MulAut ↥Bs) (c : ↥Bs) : Prop :=
  ∀ b : ↥Bs, φ b * b⁻¹ ∈ Subgroup.zpowers c

@[expose] def GGCorootPt (p : ℕ) {Bs : Subgroup G} (A : Subgroup (MulAut ↥Bs)) (c : ↥Bs) : Prop :=
  c ≠ 1 ∧ ∃ φ ∈ A, GGIsReflection p φ ∧ GGReflCentre φ c

@[expose] def GGCorootOrth (p : ℕ) {Bs : Subgroup G} (A : Subgroup (MulAut ↥Bs)) (a b : ↥Bs) :
    Prop :=
  Subgroup.zpowers a ≠ Subgroup.zpowers b ∧
    ∃ φ ∈ A, ∃ ψ ∈ A, GGIsReflection p φ ∧ GGReflCentre φ a ∧ GGIsReflection p ψ ∧
      GGReflCentre ψ b ∧ φ * ψ = ψ * φ

@[expose] def ggFixedByCentres (p : ℕ) {Bs : Subgroup G} (A : Subgroup (MulAut ↥Bs))
    (S : Set ↥Bs) : Subgroup ↥Bs where
  carrier := {b | ∀ φ ∈ A, GGIsReflection p φ → (∃ c ∈ S, GGReflCentre φ c) → φ b = b}
  one_mem' := fun φ _ _ _ => map_one φ
  mul_mem' := by
    intro a b ha hb φ hφ hr hc
    rw [map_mul, ha φ hφ hr hc, hb φ hφ hr hc]
  inv_mem' := by
    intro a ha φ hφ hr hc
    rw [map_inv, ha φ hφ hr hc]

end Vocabulary

@[expose] def ggTorusAut {L' : Type} [Group L'] [Finite L'] (A : Subgroup (MulAut L')) :
    Subgroup (MulAut ↥A) :=
  ggAutomizer (MulAut.conj : L' →* MulAut L').range A

end CFSG.StandardType

end
