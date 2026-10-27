module

public import CFSG.Quasithin.H13.HSLocOrb

public section

namespace CFSG.Quasithin.H13.LocDbl.HSLoc

open CFSG.QuasithinUnique.K1.SporadicPerm hiding img keyNat
open CFSG.Quasithin.H13.LocDbl.DcNative CFSG.Quasithin.H13.LocDbl.DcRank CFSG.Quasithin.H13.LocDbl.Dc
open CFSG.RankThree.Native

theorem act_inv_fix (g : PG) {i : ℕ} (hi : i < 100) {j : ℕ} (h : act 100 g i = j) :
    act 100 g⁻¹ j = i := by
  rw [← h, ← act_mul _ _ hi, inv_mul_cancel, act_one hi]

@[expose] def Q01 : Subgroup PG where
  carrier := {g | (act 100 g 0 = 0 ∧ act 100 g 1 = 1) ∨ (act 100 g 0 = 1 ∧ act 100 g 1 = 0)}
  one_mem' := Or.inl ⟨act_one (by norm_num), act_one (by norm_num)⟩
  mul_mem' {g h} hg hh := by
    have e0 := act_mul g h (show 0 < 100 by norm_num)
    have e1 := act_mul g h (show 1 < 100 by norm_num)
    simp only [Set.mem_setOf_eq] at hg hh ⊢
    rw [e0, e1]
    rcases hg with ⟨g0, g1⟩ | ⟨g0, g1⟩ <;> rcases hh with ⟨h0, h1⟩ | ⟨h0, h1⟩ <;>
      simp only [h0, h1, g0, g1] <;> simp
  inv_mem' {g} hg := by
    simp only [Set.mem_setOf_eq] at hg ⊢
    rcases hg with ⟨g0, g1⟩ | ⟨g0, g1⟩
    · exact Or.inl ⟨act_inv_fix g (by norm_num) g0, act_inv_fix g (by norm_num) g1⟩
    · exact Or.inr ⟨act_inv_fix g (by norm_num) g1, act_inv_fix g (by norm_num) g0⟩

@[expose] def Q0 : Subgroup PG where
  carrier := {g | act 100 g 0 = 0 ∧ act 100 g 1 = 1}
  one_mem' := ⟨act_one (by norm_num), act_one (by norm_num)⟩
  mul_mem' {g h} hg hh := by
    have e0 := act_mul g h (show 0 < 100 by norm_num)
    have e1 := act_mul g h (show 1 < 100 by norm_num)
    simp only [Set.mem_setOf_eq] at hg hh ⊢
    rw [e0, e1, hh.1, hh.2, hg.1, hg.2]
    exact ⟨rfl, rfl⟩
  inv_mem' {g} hg := ⟨act_inv_fix g (by norm_num) hg.1, act_inv_fix g (by norm_num) hg.2⟩

theorem Q01_cases {g : PG} (hg : g ∈ Q01) :
    (act 100 g 0 = 0 ∧ act 100 g 1 = 1 ∧ act 100 g⁻¹ 0 = 0 ∧ act 100 g⁻¹ 1 = 1) ∨
      (act 100 g 0 = 1 ∧ act 100 g 1 = 0 ∧ act 100 g⁻¹ 0 = 1 ∧ act 100 g⁻¹ 1 = 0) := by
  rcases hg with ⟨g0, g1⟩ | ⟨g0, g1⟩
  · exact Or.inl ⟨g0, g1, act_inv_fix g (by norm_num) g0, act_inv_fix g (by norm_num) g1⟩
  · exact Or.inr ⟨g0, g1, act_inv_fix g (by norm_num) g1, act_inv_fix g (by norm_num) g0⟩

theorem comm_fix01 {g₁ g₂ : PG} (h₁ : g₁ ∈ Q01) (h₂ : g₂ ∈ Q01) : g₁ * g₂ * g₁⁻¹ * g₂⁻¹ ∈ Q0 := by
  have key : ∀ i : ℕ, i < 2 → act 100 (g₁ * g₂ * g₁⁻¹ * g₂⁻¹) i =
      act 100 g₁ (act 100 g₂ (act 100 g₁⁻¹ (act 100 g₂⁻¹ i))) := by
    intro i hi
    have hi' : i < 100 := by omega
    have a1 := act_lt g₂⁻¹ hi'
    have a2 := act_lt g₁⁻¹ a1
    rw [act_mul _ _ hi', act_mul _ _ a1, act_mul _ _ a2]
  refine ⟨?_, ?_⟩
  · show act 100 (g₁ * g₂ * g₁⁻¹ * g₂⁻¹) 0 = 0
    rw [key 0 (by norm_num)]
    rcases Q01_cases h₁ with ⟨a1, a2, a3, a4⟩ | ⟨a1, a2, a3, a4⟩ <;>
      rcases Q01_cases h₂ with ⟨b1, b2, b3, b4⟩ | ⟨b1, b2, b3, b4⟩ <;>
      simp only [a1, a2, a3, a4, b1, b2, b3, b4]
  · show act 100 (g₁ * g₂ * g₁⁻¹ * g₂⁻¹) 1 = 1
    rw [key 1 (by norm_num)]
    rcases Q01_cases h₁ with ⟨a1, a2, a3, a4⟩ | ⟨a1, a2, a3, a4⟩ <;>
      rcases Q01_cases h₂ with ⟨b1, b2, b3, b4⟩ | ⟨b1, b2, b3, b4⟩ <;>
      simp only [a1, a2, a3, a4, b1, b2, b3, b4]


theorem Mg_le_Q01 : Mg ≤ Q01 := by
  rw [Mg, Subgroup.closure_le]
  intro g hg
  exact (mPres_gen hg).2

theorem card_fix01_le (S : Finset PG) (hS : ∀ g ∈ S, g ∈ Mg ∧ act 100 g 0 = 0 ∧ act 100 g 1 = 1) :
    S.card ≤ 5760 := by
  classical
  obtain ⟨-, -, -, hk, -⟩ := Certificates.certificate589206
  simp only [kCount, decide_eq_true_eq] at hk
  set L := mElems.toList.filter fun t => img t 0 == 0 && img t 1 == 1 with hL
  have hsub : S.image T ⊆ L.toFinset := by
    intro t ht
    obtain ⟨g, hg, rfl⟩ := Finset.mem_image.mp ht
    obtain ⟨hgM, hg0, hg1⟩ := hS g hg
    rw [List.mem_toFinset, hL, List.mem_filter]
    refine ⟨(mSpec.mem_iff g).mp hgM, ?_⟩
    simp only [Bool.and_eq_true, beq_iff_eq, img_T]
    exact ⟨hg0, hg1⟩
  have hc := Finset.card_le_card hsub
  rw [Finset.card_image_of_injective _ (fun a b hab => eq_of_T hab)] at hc
  have := List.toFinset_card_le L
  omega

end CFSG.Quasithin.H13.LocDbl.HSLoc
