module

public import CFSG.Quasithin.Background.B6Defs

public section

namespace CFSG.Quasithin

namespace E217R1

theorem not_four_dvd_card_of_two_involutions {Q : Type*} [Group Q] [Finite Q] {a b : Q}
    (ha : a * a = 1) (hb : b * b = 1) (hgen : Subgroup.closure ({a, b} : Set Q) = ⊤)
    (hcen : ∀ w : Q, w * w = 1 → w ≠ 1 → ∃ q : Q, q * w ≠ w * q) : ¬ 4 ∣ Nat.card Q := by
  have hai : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha
  have hbi : b⁻¹ = b := inv_eq_of_mul_eq_one_right hb
  set c : Q := a * b with hc
  set N : Subgroup Q := Subgroup.zpowers c with hN
  have hac : a * c * a⁻¹ = c⁻¹ := by
    rw [hc, mul_inv_rev, hai, hbi]
    calc a * (a * b) * a = (a * a) * b * a := by group
      _ = b * a := by rw [ha, one_mul]
  have hbc : b * c * b⁻¹ = c⁻¹ := by
    rw [hc, mul_inv_rev, hai, hbi]
    calc b * (a * b) * b = b * a * (b * b) := by group
      _ = b * a := by rw [hb, mul_one]
  have hnorm : ∀ t ∈ ({a, b} : Set Q), t ∈ Subgroup.normalizer (N : Set Q) := by
    intro t ht
    have key : ∀ n ∈ N, t * n * t⁻¹ ∈ N := by
      intro n hn
      obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 hn
      rw [← MulAut.conj_apply, map_zpow, MulAut.conj_apply]
      rcases ht with rfl | rfl
      · rw [hac]
        exact N.zpow_mem (N.inv_mem (Subgroup.mem_zpowers c)) j
      · rw [hbc]
        exact N.zpow_mem (N.inv_mem (Subgroup.mem_zpowers c)) j
    have hti : t⁻¹ = t := by
      rcases ht with rfl | rfl
      · exact hai
      · exact hbi
    refine B6.mem_normalizer_of_forall_mem key (fun n hn => ?_)
    have h1 := key n hn
    rw [hti] at h1 ⊢
    exact h1
  have hNnorm : N.Normal := by
    rw [← Subgroup.normalizer_eq_top_iff, eq_top_iff, ← hgen, Subgroup.closure_le]
    exact hnorm
  have hconj : ∀ n ∈ N, a * n * a⁻¹ ∈ N := fun n hn => hNnorm.conj_mem n hn a
  have hcos : ∀ q : Q, q ∈ N ∨ a * q ∈ N := by
    intro q
    have hq : q ∈ Subgroup.closure ({a, b} : Set Q) := by rw [hgen]; exact Subgroup.mem_top q
    induction hq using Subgroup.closure_induction with
    | mem x hx =>
      rcases hx with rfl | rfl
      · right
        rw [ha]
        exact N.one_mem
      · right
        exact Subgroup.mem_zpowers c
    | one => left; exact N.one_mem
    | mul x y _ _ hx hy =>
      rcases hx with hx | hx <;> rcases hy with hy | hy
      · left
        exact N.mul_mem hx hy
      · right
        have e : a * (x * y) = (a * x * a⁻¹) * (a * y) := by group
        rw [e]
        exact N.mul_mem (hconj x hx) hy
      · right
        have e : a * (x * y) = (a * x) * y := by group
        rw [e]
        exact N.mul_mem hx hy
      · left
        have e : x * y = (a * a) * (x * y) := by rw [ha, one_mul]
        have e2 : (a * a) * (x * y) = (a * (a * x) * a⁻¹) * (a * y) := by group
        rw [e, e2]
        exact N.mul_mem (hconj _ hx) hy
    | inv x _ hx =>
      rcases hx with hx | hx
      · left
        exact N.inv_mem hx
      · right
        have e : (a * (a * x) * a⁻¹)⁻¹ = a * x⁻¹ * (a⁻¹ * a⁻¹) := by group
        have h1 : a⁻¹ * a⁻¹ = 1 := by rw [hai, ha]
        rw [h1, mul_one] at e
        rw [← e]
        exact N.inv_mem (hconj _ hx)
  have hidx : N.index ≤ 2 := by
    classical
    let f : Bool → Q ⧸ N := fun t => if t then (QuotientGroup.mk a : Q ⧸ N) else QuotientGroup.mk 1
    have hf : Function.Surjective f := by
      intro y
      induction y using QuotientGroup.induction_on with
      | H q =>
        rcases hcos q with hq | hq
        · exact ⟨false, by
            simp only [f, Bool.false_eq_true, ↓reduceIte]
            exact (QuotientGroup.eq.2 (by simpa using N.inv_mem hq)).symm⟩
        · exact ⟨true, by
            simp only [f, ↓reduceIte]
            refine QuotientGroup.eq.2 ?_
            rwa [hai]⟩
    have h2 := Nat.card_le_card_of_surjective f hf
    have h3 : Nat.card (Q ⧸ N) ≤ 2 := by simpa [Nat.card_eq_fintype_card] using h2
    exact h3
  have hodd : Odd (orderOf c) := by
    by_contra hev
    rw [Nat.not_odd_iff_even] at hev
    obtain ⟨k, hk⟩ := hev
    have hk0 : 0 < k := by
      rcases Nat.eq_zero_or_pos k with h0 | h0
      · rw [h0, add_zero] at hk
        exact absurd hk (orderOf_pos c).ne'
      · exact h0
    set w : Q := c ^ k with hw
    have hw2 : w * w = 1 := by
      rw [hw, ← pow_add, ← hk]
      exact pow_orderOf_eq_one c
    have hw1 : w ≠ 1 := pow_ne_one_of_lt_orderOf hk0.ne' (by omega)
    have hwi : w⁻¹ = w := inv_eq_of_mul_eq_one_right hw2
    have hcomm : ∀ t ∈ ({a, b} : Set Q), t * w = w * t := by
      intro t ht
      have hti : t⁻¹ = t := by
        rcases ht with rfl | rfl
        · exact hai
        · exact hbi
      have h1 : t * c * t⁻¹ = c⁻¹ := by
        rcases ht with rfl | rfl
        · exact hac
        · exact hbc
      have h2 : t * w * t⁻¹ = w := by
        rw [hw, ← MulAut.conj_apply, map_pow, MulAut.conj_apply, h1, inv_pow, ← hw, hwi]
      calc t * w = t * w * t⁻¹ * t := by group
        _ = w * t := by rw [h2]
    obtain ⟨q, hq⟩ := hcen w hw2 hw1
    apply hq
    have hq' : q ∈ Subgroup.closure ({a, b} : Set Q) := by rw [hgen]; exact Subgroup.mem_top q
    have hle : Subgroup.closure ({a, b} : Set Q) ≤ Subgroup.centralizer ({w} : Set Q) := by
      rw [Subgroup.closure_le]
      intro t ht
      rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
      intro y hy
      rw [Set.mem_singleton_iff] at hy
      rw [hy]
      exact (hcomm t ht).symm
    have := Subgroup.mem_centralizer_iff.1 (hle hq') w rfl
    exact this.symm
  have hcard := Subgroup.card_mul_index N
  rw [hN, Nat.card_zpowers] at hcard
  have hidx0 : N.index ≠ 0 := Subgroup.index_ne_zero_of_finite
  intro h4
  rw [← hcard] at h4
  obtain ⟨m, hm⟩ := hodd
  interval_cases hi : N.index
  · exact absurd hidx0 (by omega)
  · rw [mul_one, hm] at h4
    omega
  · rw [hm] at h4
    omega

end E217R1

end CFSG.Quasithin
