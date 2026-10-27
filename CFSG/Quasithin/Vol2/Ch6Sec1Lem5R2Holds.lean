module

public import CFSG.Quasithin.Vol2.Ch6Sec1Lem5R2Case1
public import CFSG.Quasithin.Vol2.Ch6Sec1Lem5R2Case2
public import CFSG.Quasithin.Vol2.Ch6Sec1Lem5Rank2

public section

namespace CFSG.Quasithin.H13.R2

open CFSG.Open
open scoped commutatorElement

variable {P : Type} [Group P] [Finite P]

theorem card_omegaCenter {x y : P} {a s : MulAut P} (h : Hyp P x y a s)
    (hnc : ∃ g k : P, g * k ≠ k * g) :
    Nat.card (omegaCenter P) = 3 ∨ Nat.card (omegaCenter P) = 9 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨m, hm⟩ := IsPGroup.iff_card.mp h.p3
  have hZ9 : Nat.card (omegaCenter P) ≤ 9 := h.m3 _ omegaCenter_isElemAbelian
  have hZ1 : 1 < Nat.card (omegaCenter P) := by
    have : Nontrivial P := by
      obtain ⟨g, k, hgk⟩ := hnc
      exact ⟨⟨g * k, k * g, hgk⟩⟩
    have hm0 : 0 < m := by
      rcases Nat.eq_zero_or_pos m with h0 | h0
      · rw [h0, pow_zero] at hm
        exact absurd hm (Finite.one_lt_card (α := P)).ne'
      · exact h0
    obtain ⟨j, hj0, hj⟩ := IsPGroup.card_center_eq_prime_pow hm hm0
    obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := Subgroup.center P) 3
      (by rw [hj]; exact dvd_pow_self 3 hj0.ne')
    have hz3 : z ^ 3 = 1 := by rw [← hz]; exact pow_orderOf_eq_one z
    have hzZ : (z : P) ∈ omegaCenter P := ⟨z.2, by rw [← Subgroup.coe_pow, hz3]; rfl⟩
    rw [Subgroup.one_lt_card_iff_ne_bot]
    intro hb
    rw [hb, Subgroup.mem_bot] at hzZ
    have hz1 : z = 1 := Subtype.ext hzZ
    rw [hz1, orderOf_one] at hz
    norm_num at hz
  obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp
    (hm ▸ Subgroup.card_subgroup_dvd_card (omegaCenter P))
  rw [hi] at hZ9 hZ1 ⊢
  have hi2 : i ≤ 2 := by
    by_contra hc
    have := Nat.pow_le_pow_right (by norm_num : 0 < 3) (show 3 ≤ i by omega)
    norm_num at this
    omega
  interval_cases i
  · norm_num at hZ1
  · left; norm_num
  · right; norm_num

theorem abelian_or_card_27 :
    ∀ (n : ℕ) (P : Type) [Group P] [Finite P], Nat.card P = n → ∀ {x y : P} {a s : MulAut P},
      Hyp P x y a s → (∀ g k : P, g * k = k * g) ∨ (Nat.card P = 27 ∧ ∀ g : P, g ^ 3 = 1) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro P _ _ hn x y a s h
  by_cases hab : ∀ g k : P, g * k = k * g
  · exact Or.inl hab
  right
  have hnc : ∃ g k : P, g * k ≠ k * g := by
    push Not at hab
    exact hab
  rcases card_omegaCenter h hnc with h3 | h9
  · exact case2 h h3 hnc
  exfalso
  by_cases hcl2 : ∀ g k : P, ⁅g, k⁆ ∈ omegaCenter P
  · exact false_of_case1a h h9 hnc hcl2
  have hZΦ : omegaCenter P ≤ frattini P := fun z hz => center_le_frattini h hnc hz.1
  have hlt : Nat.card (P ⧸ omegaCenter P) < n := by
    have e1 := Subgroup.card_mul_index (omegaCenter P)
    rw [h9, hn] at e1
    have hpos : (omegaCenter P).index ≠ 0 := Subgroup.index_ne_zero_of_finite
    show (omegaCenter P).index < n
    omega
  rcases ih _ hlt (P ⧸ omegaCenter P) rfl (hyp_quot h h9 hZΦ) with hab' | ⟨h27, h3⟩
  · apply hcl2
    intro g k
    refine (QuotientGroup.eq_one_iff _).mp ?_
    rw [← QuotientGroup.mk'_apply, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
    exact hab' _ _
  · exact false_of_case1b h h9 h27 h3 hcl2

end CFSG.Quasithin.H13.R2

namespace CFSG.Quasithin.H13

open CFSG.Open
open scoped commutatorElement

theorem rankTwoThreeClassTwo_holds : RankTwoThreeClassTwo := by
  intro P _ _ hp hidx hm3 x y hgen a s hax hay hsx hsy
  have h : R2.Hyp P x y a s := ⟨hp, hidx, hm3, hgen, hax, hay, hsx, hsy⟩
  rcases R2.abelian_or_card_27 _ P rfl h with hab | hex
  · refine ⟨fun g k l => ?_, fun ⟨g, k, hgk⟩ => absurd (hab g k) hgk⟩
    rw [commutatorElement_eq_one_iff_mul_comm.mpr (hab g k), commutatorElement_one_left]
  · exact ⟨R2.comm_comm_of_card_27 hex.1, fun _ => hex⟩

end CFSG.Quasithin.H13
