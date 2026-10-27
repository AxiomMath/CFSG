module

import CFSG.Adapters.StatedClassicalSmallOrders
import CFSG.Adapters.StatedClassicalUnitaryOrders
public import CFSG.Quasithin.Vol2.Ch10SecKIK2c

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecC.C10KH

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.Vol2.Ch11.SecA
  CFSG.Assembly.LowTwoRank

@[expose] def B56Cond (N v u : ℕ) : Prop :=
  (1 ≤ v ∧ u = (2 ^ v) ^ 2 - 1) ∨
    (3 ∣ v ∧ 1 ≤ v / 3 ∧ u = ((2 ^ (v / 3)) ^ 2 - 1) * ((2 ^ (v / 3)) ^ 3 - 1)) ∨
    (4 ∣ v ∧ 1 ≤ v / 4 ∧ u = ((2 ^ (v / 4)) ^ 2 - 1) * ((2 ^ (v / 4)) ^ 4 - 1)) ∨
    (6 ∣ v ∧ 1 ≤ v / 6 ∧ u = ((2 ^ (v / 6)) ^ 6 - 1) * ((2 ^ (v / 6)) ^ 2 - 1)) ∨
    N = 360 ∨ N = 2520 ∨ N = 1080 ∨ N = 6048 ∨ N = 20160 ∨ N = 9999360

instance (N v u : ℕ) : Decidable (B56Cond N v u) := by
  unfold B56Cond
  infer_instance

theorem B56Card.cond {N v u : ℕ} (h : B56Card N) (hN : N = 2 ^ v * u) (hu : Odd u) :
    B56Cond N v u := by
  rcases h.cases hN hu with h1 | ⟨n, hn, rfl, h1⟩ | ⟨n, hn, rfl, h1⟩ | ⟨n, hn, rfl, h1⟩ | h1
  · exact Or.inl h1
  · refine Or.inr (Or.inl ⟨dvd_mul_right 3 n, ?_, ?_⟩) <;> rw [Nat.mul_div_cancel_left n
      (by norm_num)]
    · exact hn
    · exact h1
  · refine Or.inr (Or.inr (Or.inl ⟨dvd_mul_right 4 n, ?_, ?_⟩)) <;> rw [Nat.mul_div_cancel_left n
      (by norm_num)]
    · exact hn
    · exact h1
  · refine Or.inr (Or.inr (Or.inr (Or.inl ⟨dvd_mul_right 6 n, ?_, ?_⟩))) <;>
      rw [Nat.mul_div_cancel_left n (by norm_num)]
    · exact hn
    · exact h1
  · exact Or.inr (Or.inr (Or.inr (Or.inr h1)))

theorem false_of_b56_three {M N v u v' u' : ℕ} (hJ : B56Card M) (hc : N = M ∨ N = 3 * M)
    (hN : N = 2 ^ v * u) (hu : Odd u) (h1 : ¬ B56Cond N v u) (hN3 : N = 3 * (2 ^ v' * u'))
    (hu' : Odd u') (h3 : ¬ B56Cond (2 ^ v' * u') v' u') : False := by
  rcases hc with rfl | hc
  · exact h1 (hJ.cond hN hu)
  · have : M = 2 ^ v' * u' := by omega
    subst this
    exact h3 (hJ.cond rfl hu')

section Orders

variable {X : Type} [Group X]

theorem card_L225 (h : IsPSL 2 5 2 X) : Nat.card X = 7800 :=
  CFSG.Open.StatedAPI.card_of_statedClassicalModel_psl_two_twenty_five h

theorem card_L249 (h : IsPSL 2 7 2 X) : Nat.card X = 58800 :=
  CFSG.Open.StatedAPI.card_of_statedClassicalModel_psl_two_forty_nine h

theorem card_L35 (h : IsPSL 3 5 1 X) : Nat.card X = 372000 :=
  CFSG.Open.StatedAPI.card_of_statedClassicalModel_psl_three_five h

theorem card_L37 (h : IsPSL 3 7 1 X) : Nat.card X = 1876896 :=
  CFSG.Open.StatedAPI.card_of_statedClassicalModel_psl_three_seven h

theorem card_U35 (h : IsPSU 3 5 1 X) : Nat.card X = 126000 :=
  CFSG.Open.StatedAPI.card_of_statedClassicalModel_psu_three_five h

theorem card_U37 (h : IsPSU 3 7 1 X) : Nat.card X = 5663616 :=
  CFSG.Open.StatedAPI.card_of_statedClassicalModel_psu_three_seven h

theorem card_SL35 (h : IsSL3 5 X) : Nat.card X = 372000 := by
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ := h
  rw [Nat.card_congr e.toEquiv, card_statedSL_three1527d, hK]
  norm_num

theorem card_SL37 (h : IsSL3 7 X) : Nat.card X = 5630688 := by
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ := h
  rw [Nat.card_congr e.toEquiv, card_statedSL_three1527d, hK]
  norm_num

theorem card_SU3 {p : ℕ} (hp : p.Prime) (h : IsSU3 p X) :
    Nat.card X = p ^ 3 * (p ^ 2 - 1) * (p ^ 3 + 1) := by
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ := h
  have : Fact p.Prime := ⟨hp⟩
  have hK' : Nat.card K = (p ^ 1) ^ 2 := by rw [pow_one]; exact hK
  have : CharP K p := CFSG.LieType.Steinberg.charP_of_card_eq_sq_pow hp hK'
  have hc := CFSG.SectionRank.OddCover.card_statedSU_three (K := K) (p := p) (f := 1) hK'
  simp only [pow_one] at hc
  rw [Nat.card_congr e.toEquiv, hc]

theorem card_SU35 (h : IsSU3 5 X) : Nat.card X = 378000 := by
  rw [card_SU3 (by norm_num) h]
  norm_num

theorem card_SU37 (h : IsSU3 7 X) : Nat.card X = 5663616 := by
  rw [card_SU3 (by norm_num) h]
  norm_num

end Orders

end CFSG.Quasithin.Vol2.Ch10.SecC.C10KH
