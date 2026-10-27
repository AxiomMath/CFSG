module

public import CFSG.RankThree.PartTwo.Sec21.FF79Lemma42CTypesG
public import CFSG.RankThree.PartTwo.Sec21.FF79Lemma42CTypesT

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF79

open CFSG.GroupTheory.GL52 Matrix CFSG.RankThree.PartTwo.Sec21.FF79.TypesG

open scoped Pointwise

variable {G : Type} [Group G]

private theorem le_nor_of_comm {X : Type} [Group X] {A K : Subgroup X}
    (hcomm : ∀ a ∈ A, ∀ k ∈ K, a * k = k * a) : A ≤ Nor K := fun a ha =>
  Subgroup.mem_normalizer_iff.mpr fun k => by
    constructor
    · intro hk
      rw [hcomm a ha k hk, mul_inv_cancel_right]
      exact hk
    · intro hk
      have h1 : a⁻¹ * (a * k * a⁻¹) = a * k * a⁻¹ * a⁻¹ := hcomm a⁻¹ (inv_mem ha) _ hk
      have h2 : a⁻¹ * (a * k * a⁻¹) = k * a⁻¹ := by group
      rw [h2] at h1
      rw [mul_right_cancel h1]
      exact hk

theorem lay_cen_data {J : Subgroup G} (e : ↥J ≃* G52) {x : G} (hx : x ∈ J)
    (h3 : orderOf x = 3) :
    ((Matrix.trace ((e ⟨x, hx⟩ : G52) : M5) = 1 ∧ IsLnq 2 2 2 (Lay (J ⊓ Cen x)) ∧
        ¬ IsLnq 3 2 1 (Lay (J ⊓ Cen x))) ∨
      (Matrix.trace ((e ⟨x, hx⟩ : G52) : M5) = 0 ∧ IsLnq 3 2 1 (Lay (J ⊓ Cen x)) ∧
        ¬ IsLnq 2 2 2 (Lay (J ⊓ Cen x)))) ∧
    (∀ z ∈ Lay (J ⊓ Cen x), orderOf z = 3 → ∃ hz : z ∈ J,
      Matrix.trace ((e ⟨z, hz⟩ : G52) : M5) = Matrix.trace ((e ⟨x, hx⟩ : G52) : M5)) ∧
    (∀ w ∈ J ⊓ Cen x, ∃ i : ℤ, ∃ l ∈ Lay (J ⊓ Cen x), w = x ^ i * l) ∧
    (∀ z ∈ Lay (J ⊓ Cen x), z ∈ Subgroup.zpowers x → z = 1) := by
  have hy3 : orderOf (e ⟨x, hx⟩) = 3 := by
    rw [MulEquiv.orderOf_eq]
    exact (orderOf_submonoid (⟨x, hx⟩ : ↥J)).symm.trans h3
  obtain ⟨K, hK, hdp, htype, htr⟩ := g52_type hy3
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [isLnq_lay_cen_iff e x hx (n := 2) (p := 2) (f := 2),
      isLnq_lay_cen_iff e x hx (n := 3) (p := 2) (f := 1), hK]
    rcases htype with ⟨ht, hL⟩ | ⟨ht, hL⟩
    · left
      exact ⟨ht, hL, fun h => not_isLnq_both K ⟨hL, h⟩⟩
    · right
      exact ⟨ht, hL, fun h => not_isLnq_both K ⟨h, hL⟩⟩
  · intro z hz hz3
    obtain ⟨hzJ, hzK⟩ := (mem_lay_cen_iff e x hx z).mp hz
    refine ⟨hzJ, htr _ (hK ▸ hzK) ?_⟩
    rw [MulEquiv.orderOf_eq]
    exact (orderOf_submonoid (⟨z, hzJ⟩ : ↥J)).symm.trans hz3
  · intro w hw
    have hwy : e ⟨w, hw.1⟩ ∈ Cen (e ⟨x, hx⟩) := (cenEquiv e x hx ⟨w, hw⟩).2
    rw [← hdp.1] at hwy
    have hmul : ((Subgroup.zpowers (e ⟨x, hx⟩) ⊔ K : Subgroup G52) : Set G52) =
        (Subgroup.zpowers (e ⟨x, hx⟩) : Set G52) * (K : Set G52) := by
      exact Subgroup.coe_mul_of_left_le_normalizer_right _ _ (le_nor_of_comm hdp.2.2)
    have hwy' : e ⟨w, hw.1⟩ ∈ ((Subgroup.zpowers (e ⟨x, hx⟩) ⊔ K : Subgroup G52) : Set G52) :=
      hwy
    rw [hmul] at hwy'
    obtain ⟨a, ha, k, hk, hak⟩ := hwy'
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
    refine ⟨i, (e.symm k : ↥J), ?_, ?_⟩
    · rw [mem_lay_cen_iff e x hx]
      refine ⟨(e.symm k).2, ?_⟩
      rw [hK]
      simpa using hk
    · have h1 : (⟨w, hw.1⟩ : ↥J) = e.symm (e ⟨x, hx⟩ ^ i * k) := by
        have hak' : e ⟨w, hw.1⟩ = e ⟨x, hx⟩ ^ i * k := hak.symm
        rw [← hak']; simp
      have h2 := congrArg Subtype.val h1
      simpa [map_mul, map_zpow] using h2
  · intro z hz hzx
    obtain ⟨hzJ, hzK⟩ := (mem_lay_cen_iff e x hx z).mp hz
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hzx
    have hzy : e ⟨x ^ i, hzJ⟩ = e ⟨x, hx⟩ ^ i := by
      rw [← map_zpow]
      rfl
    rw [hzy, hK] at hzK
    have h1 : e ⟨x, hx⟩ ^ i ∈ Subgroup.zpowers (e ⟨x, hx⟩) ⊓ K :=
      ⟨Subgroup.zpow_mem_zpowers _ _, hzK⟩
    rw [hdp.2.1, Subgroup.mem_bot] at h1
    have h2 := e.injective ((hzy.trans h1).trans (map_one e).symm)
    exact congrArg Subtype.val h2

end CFSG.RankThree.PartTwo.Sec21.FF79
