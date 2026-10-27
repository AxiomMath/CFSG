module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightS1T3KbarIdxA

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open Subgroup

theorem s16t3_index_le_two_of_normIdx {Q : Type*} [Group Q] [Finite Q] {Γ : Subgroup Q}
    (h : s16t3_normIdx Γ) :
    (Γ.subgroupOf (Subgroup.normalizer (Γ : Set Q))).index ≤ 2 := by
  classical
  set N := Subgroup.normalizer (Γ : Set Q) with hN
  haveI : Fintype (↥N ⧸ Γ.subgroupOf N) := Fintype.ofFinite _
  by_contra hcon
  rw [not_le] at hcon
  have hcard : 2 < Fintype.card (↥N ⧸ Γ.subgroupOf N) := by
    rw [← Nat.card_eq_fintype_card, ← Subgroup.index_eq_card]
    exact hcon
  obtain ⟨q₁, q₂, q₃, h12, h13, h23⟩ := Fintype.two_lt_card_iff.mp hcard
  obtain ⟨M₁, rfl⟩ := QuotientGroup.mk_surjective q₁
  obtain ⟨M₂, rfl⟩ := QuotientGroup.mk_surjective q₂
  obtain ⟨M₃, rfl⟩ := QuotientGroup.mk_surjective q₃
  have key : ∀ x y : ↥N, (QuotientGroup.mk x : ↥N ⧸ Γ.subgroupOf N) ≠ QuotientGroup.mk y →
      ((x : Q)⁻¹ * (y : Q)) ∉ Γ := by
    intro x y hxy hmem
    exact hxy (QuotientGroup.eq.mpr (Subgroup.mem_subgroupOf.mpr hmem))
  rcases h M₁ M₂ M₃ M₁.2 M₂.2 M₃.2 with h' | h' | h'
  · exact key M₁ M₂ h12 h'
  · exact key M₁ M₃ h13 h'
  · exact key M₂ M₃ h23 h'

theorem s16t3_normIdx_map_mulEquiv {Q₁ Q₂ : Type*} [Group Q₁] [Group Q₂] (e : Q₁ ≃* Q₂)
    {Γ : Subgroup Q₁} (h : s16t3_normIdx Γ) : s16t3_normIdx (Γ.map e.toMonoidHom) := by
  intro M₁ M₂ M₃ hM₁ hM₂ hM₃
  have key : ∀ M ∈ Subgroup.normalizer ((Γ.map e.toMonoidHom : Subgroup Q₂) : Set Q₂),
      e.symm M ∈ Subgroup.normalizer (Γ : Set Q₁) := by
    intro M hM
    have h1 : e.symm M ∈ (Subgroup.normalizer
        ((Γ.map e.toMonoidHom : Subgroup Q₂) : Set Q₂)).map e.symm.toMonoidHom :=
      ⟨M, hM, by simp⟩
    have h2 := Subgroup.le_normalizer_map
      (H := Γ.map e.toMonoidHom) (f := e.symm.toMonoidHom) h1
    have h3 : (Γ.map e.toMonoidHom).map e.symm.toMonoidHom = Γ := by
      rw [Subgroup.map_map]
      convert Subgroup.map_id Γ using 2
      ext x
      simp
    rwa [h3] at h2
  rcases h (e.symm M₁) (e.symm M₂) (e.symm M₃)
    (key M₁ hM₁) (key M₂ hM₂) (key M₃ hM₃) with h' | h' | h'
  · left
    have := Subgroup.mem_map_of_mem e.toMonoidHom h'
    simpa [map_inv, map_mul] using this
  · right; left
    have := Subgroup.mem_map_of_mem e.toMonoidHom h'
    simpa [map_inv, map_mul] using this
  · right; right
    have := Subgroup.mem_map_of_mem e.toMonoidHom h'
    simpa [map_inv, map_mul] using this

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
