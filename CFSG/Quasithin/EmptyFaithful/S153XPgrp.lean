module

public import Mathlib.GroupTheory.Nilpotent

public section

namespace CFSG.Quasithin.X1469

theorem exists_fixed_mod {G : Type} [Group G] [Finite G] {S E N : Subgroup G}
    (hS : IsPGroup 2 S) (hES : E ≤ S) (hEn : S ≤ Subgroup.normalizer (E : Set G))
    (hNn : S ≤ Subgroup.normalizer (N : Set G)) (hNE : ¬ E ≤ N) :
    ∃ x ∈ E, x ∉ N ∧ ∀ y ∈ S, x * y * x⁻¹ * y⁻¹ ∈ N := by
  have hN'n : S ≤ Subgroup.normalizer ((N ⊓ E : Subgroup G) : Set G) :=
    (le_inf hNn hEn).trans Subgroup.inf_normalizer_le_normalizer_inf
  have hM : ((N ⊓ E).subgroupOf S).Normal := Subgroup.normal_subgroupOf_of_le_normalizer hN'n
  have hEnorm : (E.subgroupOf S).Normal := Subgroup.normal_subgroupOf_of_le_normalizer hEn
  have : Group.IsNilpotent (↥S ⧸ (N ⊓ E).subgroupOf S) := (hS.to_quotient _).isNilpotent
  let π : ↥S →* ↥S ⧸ (N ⊓ E).subgroupOf S := QuotientGroup.mk' _
  let Ē : Subgroup (↥S ⧸ (N ⊓ E).subgroupOf S) := (E.subgroupOf S).map π
  have : Ē.Normal := Subgroup.Normal.map hEnorm π (QuotientGroup.mk'_surjective _)
  have hĒ : Ē ≠ ⊥ := by
    intro hbot
    apply hNE
    intro e he
    have hmem : π ⟨e, hES he⟩ ∈ Ē :=
      Subgroup.mem_map_of_mem π (Subgroup.mem_subgroupOf.2 he)
    rw [hbot, Subgroup.mem_bot] at hmem
    have h1 : (⟨e, hES he⟩ : ↥S) ∈ (N ⊓ E).subgroupOf S := (QuotientGroup.eq_one_iff _).1 hmem
    exact (Subgroup.mem_inf.1 (Subgroup.mem_subgroupOf.1 h1)).1
  obtain ⟨⟨q, hqĒ, hqZ⟩, hq1⟩ :=
    Subgroup.ne_bot_iff_exists_ne_one.1 (Group.IsNilpotent.inf_center_ne_bot_of_normal hĒ)
  obtain ⟨h, hhE, rfl⟩ := hqĒ
  have hxE : (h : G) ∈ E := Subgroup.mem_subgroupOf.1 hhE
  refine ⟨h, hxE, fun hxN => hq1 (Subtype.ext ?_), fun y hy => ?_⟩
  · exact (QuotientGroup.eq_one_iff _).2
      (Subgroup.mem_subgroupOf.2 (Subgroup.mem_inf.2 ⟨hxN, hxE⟩))
  · have hcomm := Subgroup.mem_center_iff.1 hqZ (π ⟨y, hy⟩)
    have h1 : h * ⟨y, hy⟩ * h⁻¹ * ⟨y, hy⟩⁻¹ ∈ (N ⊓ E).subgroupOf S := by
      refine (QuotientGroup.eq_one_iff _).1 ?_
      change π (h * ⟨y, hy⟩ * h⁻¹ * ⟨y, hy⟩⁻¹) = 1
      rw [map_mul, map_mul, map_mul, map_inv, map_inv, mul_inv_eq_one, mul_inv_eq_iff_eq_mul]
      exact hcomm.symm
    exact (Subgroup.mem_inf.1 (Subgroup.mem_subgroupOf.1 h1)).1

end CFSG.Quasithin.X1469
