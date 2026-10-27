module

public import CFSG.Quasithin.Background.C116Two.NatCount

public section

namespace CFSG.Quasithin.C116Two

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Open
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem fixMod_le_centralizer {H L A : Subgroup G} (hL : IsChiBlock H L) (hA : IsElemAbelian 2 A)
    (hAN : A ≤ Subgroup.normalizer (L : Set G))
    (hoff : Nat.card (blockU L) ≤ (A ⊓ Subgroup.centralizer (blockU L : Set G)).relIndex A *
      Nat.card ↥(blockU L ⊓ Subgroup.centralizer (A : Set G))) :
    ∀ u ∈ blockU L, (∀ a ∈ A, ⁅u, a⁆ ∈ blockZ L) → ∀ a ∈ A, u * a = a * u := by
  intro u hu huZ a ha
  have hcount := natCount_chiBlock hL hA hAN
  have hi : (A ⊓ Subgroup.centralizer (blockU L : Set G)).relIndex A ≠ 0 := by
    haveI : (A ⊓ Subgroup.centralizer (blockU L : Set G)).IsFiniteRelIndex A :=
      Subgroup.isFiniteRelIndex_of_finiteIndex
    exact Subgroup.relIndex_ne_zero
  have hNM : Nat.card {v : G // v ∈ blockU L ∧ ∀ b ∈ A, ⁅v, b⁆ ∈ blockZ L} ≤
      Nat.card ↥(blockU L ⊓ Subgroup.centralizer (A : Set G)) :=
    le_of_mul_le_mul_left (hcount.trans hoff) (Nat.pos_of_ne_zero hi)
  have hSY : ((blockU L ⊓ Subgroup.centralizer (A : Set G) : Subgroup G) : Set G) ⊆
      {v : G | v ∈ blockU L ∧ ∀ b ∈ A, ⁅v, b⁆ ∈ blockZ L} := by
    intro v hv
    rw [SetLike.mem_coe, Subgroup.mem_inf] at hv
    show v ∈ blockU L ∧ ∀ b ∈ A, ⁅v, b⁆ ∈ blockZ L
    refine ⟨hv.1, fun b hb => ?_⟩
    have hcomm : b * v = v * b := Subgroup.mem_centralizer_iff.mp hv.2 b hb
    rw [commutatorElement_eq_one_iff_mul_comm.mpr hcomm.symm]
    exact one_mem _
  have heq := Set.eq_of_subset_of_ncard_le hSY hNM
  have huY : u ∈ {v : G | v ∈ blockU L ∧ ∀ b ∈ A, ⁅v, b⁆ ∈ blockZ L} := ⟨hu, huZ⟩
  rw [← heq] at huY
  have huC : u ∈ Subgroup.centralizer (A : Set G) :=
    (Subgroup.mem_inf.mp (SetLike.mem_coe.mp huY)).2
  exact (Subgroup.mem_centralizer_iff.mp huC a ha).symm

end CFSG.Quasithin.C116Two
