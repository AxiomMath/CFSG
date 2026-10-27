module

public import CFSG.Monster.Existence.StdOdd.Main

public section

namespace CFSG.Monster.Existence.StdOdd

open CFSG Subgroup

section Arith

theorem le_seven_of_dvd {n a : ℕ} (h3 : 3 ^ a ∣ n) (hdvd : n ∣ 3 ^ 7 * 5 ^ 2 * 7 * 11 * 19) :
    a ≤ 7 :=
  le_of_pow_dvd_mul (m := 5 ^ 2 * 7 * 11 * 19) (by norm_num)
    (by simpa only [mul_assoc] using h3.trans hdvd)

theorem bound3_of_shape {n a : ℕ} (h : CaseBShape n a) (e13 : ¬ 13 ∣ n) (e11 : ¬ 11 ∣ n)
    (hdvd : n ∣ 3 ^ 7 * 5 ^ 2 * 7 * 11 * 19) : n ≤ 15309 := by
  rcases h with h | ⟨h, ha⟩ | ⟨k, hk, h, ha⟩ | ⟨k, hk, h, ha⟩ | ⟨k, hk, h, ha⟩
  · have h2 : a ≤ 7 := le_seven_of_dvd (h ▸ dvd_rfl) hdvd
    rw [h]
    calc 3 ^ a ≤ 3 ^ 7 := Nat.pow_le_pow_right (by norm_num) h2
      _ ≤ 15309 := by norm_num
  · have h2 : a ≤ 7 := le_seven_of_dvd (h ▸ Dvd.intro 5 rfl) hdvd
    rw [h]
    calc 3 ^ a * 5 ≤ 3 ^ 7 * 5 := Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by norm_num) h2)
      _ ≤ 15309 := by norm_num
  · rcases ha with rfl | rfl | rfl <;> rcases hk with rfl | rfl
    all_goals first
      | (rw [h]; norm_num; done)
      | (exfalso; rw [h] at hdvd; revert hdvd; decide)
  · exact absurd ⟨3 ^ a * k, by rw [h]; ring⟩ e11
  · exact absurd ⟨3 ^ a * k, by rw [h]; ring⟩ e13

end Arith

section Abstract

variable {G : Type*} [Group G] [Finite G]

theorem odd_bound_seven_abstract (hodd : Odd (Nat.card G))
    (hdvd : Nat.card G ∣ 3 ^ 9 * 5 ^ 2 * 7 ^ 2 * 11 * 13 * 17 * 19) (hC : CentralizerFacts G)
    (hT : ThreeLocalFacts G) (h7 : Nat.card G ∣ 3 ^ 7 * 5 ^ 2 * 7 * 11 * 19) :
    Nat.card G ≤ 15309 := by
  have hsolv : Group.IsSolvable G := CFSG.FeitThompson.isSolvable_of_odd_natCard _ hodd
  by_cases hA : ∃ r : ℕ, r.Prime ∧ r ≠ 3 ∧ pCore r G ≠ ⊥
  · obtain ⟨r, hr, hr3, hne⟩ := hA
    have : Fact r.Prime := ⟨hr⟩
    have h := card_le_of_normal_subgroup hodd hdvd hC hr3 (S := pCore r G) pCore_isPGroup hne
    have h49 : ¬ 7 ^ 2 ∣ Nat.card G := fun h49 => by
      have := h49.trans h7
      revert this
      decide
    have := h.2 h49
    omega
  · push Not at hA
    obtain ⟨a, ctx, hmax⟩ := caseB_ctx hsolv hodd hdvd hC hA
    have hshape := caseB_shape ctx hsolv hmax
    have e11 : ¬ 11 ∣ Nat.card G := by
      intro h11
      have : Fact (Nat.Prime 11) := ⟨by norm_num⟩
      obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' (G := G) 11 h11
      exact ctx.e4_false hT (ctx.feasible11 hg) hg
    exact bound3_of_shape hshape
      (fun h13 => by
        have := h13.trans h7
        revert this
        decide) e11 h7

end Abstract

section Final

variable {R : Type*} [Group R] [Finite R]

theorem odd_bound_seven_of_facts
    (hR : Nat.card R = 2 ^ 36 * 3 ^ 9 * 5 ^ 2 * 7 ^ 2 * 11 * 13 * 17 * 19)
    (hC : CentralizerFacts R) (hT : ThreeLocalFacts R) :
    ∀ M : Subgroup R, Odd (Nat.card M) → Nat.card M ∣ 3 ^ 7 * 5 ^ 2 * 7 * 11 * 19 →
      Nat.card M ≤ 15309 := fun M hM hd =>
  odd_bound_seven_abstract hM (card_dvd_of_odd hR M hM) (hC.restrict M) (hT.restrict M) hd

theorem stdOddBounds3_of_facts
    (hR : Nat.card R = 2 ^ 36 * 3 ^ 9 * 5 ^ 2 * 7 ^ 2 * 11 * 13 * 17 * 19)
    (hC : CentralizerFacts R) (hT : ThreeLocalFacts R) :
    (∀ M : Subgroup R, Odd (Nat.card M) → Nat.card M ≤ 54463) ∧
    (∀ M : Subgroup R, Odd (Nat.card M) → Nat.card M ∣ 3 ^ 6 * 5 ^ 2 * 7 * 11 * 19 →
      Nat.card M ≤ 9477) ∧
    (∀ M : Subgroup R, Odd (Nat.card M) → Nat.card M ∣ 3 ^ 7 * 5 ^ 2 * 7 * 11 * 19 →
      Nat.card M ≤ 15309) :=
  ⟨(odd_bounds_of_facts hR hC hT).1, (odd_bounds_of_facts hR hC hT).2,
    odd_bound_seven_of_facts hR hC hT⟩

end Final

end CFSG.Monster.Existence.StdOdd
