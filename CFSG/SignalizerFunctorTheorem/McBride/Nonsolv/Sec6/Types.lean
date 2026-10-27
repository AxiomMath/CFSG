module

public import Mathlib
public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.Sec6.Lines
public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.Sec6.L69

public section

open CFSG.Open

universe u

namespace CFSG.SignalizerFunctorTheorem.McBride.Nonsolv

namespace Counterexample

variable {p : ℕ} {G : Type u} [Group G] [Finite G] {A : Subgroup G} {θ : G → Subgroup G}

theorem card_lcal_mul_card_bN_line
    (h : Counterexample p A θ) {F : Subgroup G}
    (hF : F ∈ signalizerFunctorEk p 1 A) :
    Nat.card (lcal (thetaOf θ F)) * Nat.card (bN A θ F) = p ^ 3 :=
  h.card ▸ h.lemma_6_9_c hF.1 (h.ne_bot_of_mem_E1 hF)

theorem le_bN
    (h : Counterexample p A θ) {F : Subgroup G}
    (hF : F ∈ signalizerFunctorEk p 1 A) : F ≤ bN A θ F := by
  have hF0 := h.ne_bot_of_mem_E1 hF
  have hcard := h.card_lcal_mul_card_bN_line hF
  have hpos : 0 < Nat.card (lcal (thetaOf θ F)) := by
    rcases Nat.eq_zero_or_pos (Nat.card (lcal (thetaOf θ F))) with h0 | h0
    · rw [h0, zero_mul] at hcard
      exact absurd hcard.symm (pow_pos h.prime.pos 3).ne'
    · exact h0
  obtain ⟨⟨L, hL⟩, -⟩ := Nat.card_pos_iff.mp hpos
  have hb := h.lemma_6_9_b hF.1 hF0 L hL
  intro f hf
  rw [hb]
  have hLH : L ≤ thetaOf θ F := lcal_le hL
  have hHF : thetaOf θ F ≤ Subgroup.centralizer (F : Set G) :=
    h.isFunctor.thetaOf_le_centralizer hF.1
  have hfC : f ∈ Subgroup.centralizer (L : Set G) :=
    (Subgroup.le_centralizer_iff.mp (hLH.trans hHF)) hf
  exact Subgroup.mem_inf.mpr ⟨hF.1 hf, Subgroup.centralizer_le_normalizer _ hfC⟩

omit [Finite G] in
theorem bN_le (A : Subgroup G) (θ : G → Subgroup G) (F : Subgroup G) : bN A θ F ≤ A :=
  inf_le_left

theorem card_bN_eq_pow
    (h : Counterexample p A θ) {F : Subgroup G}
    (hF : F ∈ signalizerFunctorEk p 1 A) :
    ∃ j, 1 ≤ j ∧ j ≤ 3 ∧ Nat.card (bN A θ F) = p ^ j := by
  obtain ⟨j, hj, hjeq⟩ := h.exists_card_eq_pow_of_le (bN_le A θ F)
  refine ⟨j, ?_, hj, hjeq⟩
  by_contra hlt
  have hj0 : j = 0 := by omega
  have := Subgroup.card_le_of_le (h.le_bN hF)
  rw [hF.2, hjeq, hj0] at this
  simp at this
  exact absurd this (not_le.mpr h.prime.one_lt)

theorem mem_sSet_iff
    (h : Counterexample p A θ) {F : Subgroup G}
    (hF : F ∈ signalizerFunctorEk p 1 A) {i : ℕ} (hi : i ≤ 3) :
    F ∈ sSet p A θ i ↔ Nat.card (bN A θ F) = p ^ (3 - i) := by
  have hc := h.card_lcal_mul_card_bN_line hF
  have hp0 := h.prime.pos
  have hsum : p ^ i * p ^ (3 - i) = p ^ 3 := by rw [← pow_add]; congr 1; omega
  constructor
  · rintro ⟨-, hci⟩
    rw [hci] at hc
    exact Nat.eq_of_mul_eq_mul_left (pow_pos hp0 i) (hc.trans hsum.symm)
  · intro hm
    refine ⟨hF, ?_⟩
    rw [hm] at hc
    exact Nat.eq_of_mul_eq_mul_right (pow_pos hp0 (3 - i)) (hc.trans hsum.symm)

theorem line_cases
    (h : Counterexample p A θ) {F : Subgroup G}
    (hF : F ∈ signalizerFunctorEk p 1 A) :
    F ∈ sSet p A θ 0 ∨ F ∈ sSet p A θ 1 ∨ F ∈ sSet p A θ 2 := by
  obtain ⟨j, hj1, hj3, hj⟩ := h.card_bN_eq_pow hF
  have hj' : j = 3 ∨ j = 2 ∨ j = 1 := by omega
  rcases hj' with rfl | rfl | rfl
  · exact Or.inl ((h.mem_sSet_iff hF (by norm_num)).mpr (by simpa using hj))
  · exact Or.inr (Or.inl ((h.mem_sSet_iff hF (by norm_num)).mpr (by simpa using hj)))
  · exact Or.inr (Or.inr ((h.mem_sSet_iff hF (by norm_num)).mpr (by simpa using hj)))

theorem mem_sSet_two_iff
    (h : Counterexample p A θ) {F : Subgroup G}
    (hF : F ∈ signalizerFunctorEk p 1 A) : F ∈ sSet p A θ 2 ↔ bN A θ F = F := by
  rw [h.mem_sSet_iff hF (by norm_num)]
  constructor
  · intro hm
    refine (Subgroup.eq_of_le_of_card_ge (h.le_bN hF) ?_).symm
    rw [hm, hF.2]
  · intro hm
    rw [hm, hF.2]

theorem mem_sSet_zero_iff
    (h : Counterexample p A θ) {F : Subgroup G}
    (hF : F ∈ signalizerFunctorEk p 1 A) : F ∈ sSet p A θ 0 ↔ bN A θ F = A := by
  rw [h.mem_sSet_iff hF (by norm_num)]
  constructor
  · intro hm
    exact Subgroup.eq_of_le_of_card_ge (bN_le A θ F) (by rw [hm, h.card])
  · intro hm
    rw [hm, h.card]

theorem mem_sSet_one_iff
    (h : Counterexample p A θ) {F : Subgroup G}
    (hF : F ∈ signalizerFunctorEk p 1 A) :
    F ∈ sSet p A θ 1 ↔ Nat.card (bN A θ F) = p ^ 2 := by
  rw [h.mem_sSet_iff hF (by norm_num)]

omit [Finite G] in
theorem sSet_subset (i : ℕ) : sSet p A θ i ⊆ signalizerFunctorEk p 1 A := fun _ hF => hF.1

end Counterexample

end CFSG.SignalizerFunctorTheorem.McBride.Nonsolv
