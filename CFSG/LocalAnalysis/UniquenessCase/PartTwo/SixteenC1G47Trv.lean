module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.SubgroupConjAction
public import Mathlib.GroupTheory.PGroup

public section

open Classical
open scoped CharTwo IsMulCommutative

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open Subgroup

private def zpowTwo {G : Type*} [Group G] (a : G) (m : ZMod 2) : G :=
  if m = 0 then 1 else a

private lemma zpowTwo_zero {G : Type*} [Group G] (a : G) : zpowTwo a 0 = 1 := by
  simp [zpowTwo]

private lemma zpowTwo_one {G : Type*} [Group G] (a : G) : zpowTwo a 1 = a := by
  simp [zpowTwo]

private lemma one_add_one_zmod2 : (1 : ZMod 2) + 1 = 0 := by decide

private lemma zmod2_eq_zero_or_one (m : ZMod 2) : m = 0 ∨ m = 1 := by decide +revert

private lemma zpowTwo_add {G : Type*} [Group G] {a : G} (ha : a * a = 1) (m n : ZMod 2) :
    zpowTwo a (m + n) = zpowTwo a m * zpowTwo a n := by
  rcases eq_or_ne m 0 with rfl | hm
  · simp [zpowTwo]
  rcases eq_or_ne n 0 with rfl | hn
  · simp [zpowTwo]
  have hm1 : m = 1 := by
    rcases zmod2_eq_zero_or_one m with h0 | h1
    · exact absurd h0 hm
    · exact h1
  have hn1 : n = 1 := by
    rcases zmod2_eq_zero_or_one n with h0 | h1
    · exact absurd h0 hn
    · exact h1
  rw [hm1, hn1, one_add_one_zmod2]
  simp [zpowTwo, ha]

private lemma zpowTwo_injective {G : Type*} [Group G] {a : G} (ha : a ≠ 1) :
    Function.Injective (zpowTwo a) := by
  intro m n h
  rcases zmod2_eq_zero_or_one m with hm0 | hm1
  · rcases zmod2_eq_zero_or_one n with hn0 | hn1
    · exact hm0.trans hn0.symm
    · simp only [hm0, hn1, zpowTwo_zero, zpowTwo_one] at h
      exact absurd h.symm ha
  · rcases zmod2_eq_zero_or_one n with hn0 | hn1
    · simp only [hm1, hn0, zpowTwo_zero, zpowTwo_one] at h
      exact absurd h ha
    · exact hm1.trans hn1.symm

private noncomputable def trvExp {E : Type*} [Group E] (σ : MulAut E) (x : E) : ZMod 2 :=
  if σ x = x then 0 else 1

theorem s16c1_G47_two_transv {E : Type*} [Group E] (hE : ∀ x : E, x * x = 1) {σ τ : MulAut E}
    {a b : E} (ha : a ≠ 1) (hb : b ≠ 1) (hab : a ≠ b) (hσ : ∀ x, σ x = x ∨ σ x = x * a)
    (hτ : ∀ x, τ x = x ∨ τ x = x * b) (hσ1 : σ ≠ 1) (hτ1 : τ ≠ 1) :
    orderOf (σ * τ) = 2 ∨ orderOf (σ * τ) = 3 ∨ orderOf (σ * τ) = 4 := by
  have hcomm : ∀ x y : E, x * y = y * x := by
    intro x y
    have hxy : (x * y)⁻¹ = x * y := inv_eq_of_mul_eq_one_right (hE (x * y))
    rw [mul_inv_rev, inv_eq_of_mul_eq_one_right (hE y),
      inv_eq_of_mul_eq_one_right (hE x)] at hxy
    exact hxy.symm
  haveI : IsMulCommutative E := IsMulCommutative.of_comm hcomm
  have ha2 : a * a = 1 := hE a
  have hb2 : b * b = 1 := hE b
  have hσa : σ a = a := by
    rcases hσ a with h | h
    · exact h
    · exact absurd (σ.injective (by rw [h, ha2, map_one])) ha
  have hτb : τ b = b := by
    rcases hτ b with h | h
    · exact h
    · exact absurd (τ.injective (by rw [h, hb2, map_one])) hb
  have hσ2 : ∀ x, σ (σ x) = x := by
    intro x
    rcases hσ x with h | h
    · rw [h, h]
    · rw [h, map_mul, hσa, h, mul_assoc, ha2, mul_one]
  have hτ2 : ∀ x, τ (τ x) = x := by
    intro x
    rcases hτ x with h | h
    · rw [h, h]
    · rw [h, map_mul, hτb, h, mul_assoc, hb2, mul_one]
  have hσae : ∀ m : ZMod 2, σ (zpowTwo a m) = zpowTwo a m := by
    intro m
    rcases zmod2_eq_zero_or_one m with rfl | rfl
    · rw [zpowTwo_zero, map_one]
    · rw [zpowTwo_one, hσa]
  have hτbe : ∀ m : ZMod 2, τ (zpowTwo b m) = zpowTwo b m := by
    intro m
    rcases zmod2_eq_zero_or_one m with rfl | rfl
    · rw [zpowTwo_zero, map_one]
    · rw [zpowTwo_one, hτb]
  have hs : ∀ x, σ x = x * zpowTwo a (trvExp σ x) := by
    intro x
    rcases hσ x with h | h
    · rw [show trvExp σ x = 0 by simp [trvExp, h], zpowTwo_zero, mul_one, h]
    · have hne : σ x ≠ x := by
        rw [h]
        intro hc
        exact ha (mul_left_cancel (by rw [mul_one]; exact hc))
      rw [show trvExp σ x = 1 by simp [trvExp, hne], zpowTwo_one, h]
  have ht : ∀ x, τ x = x * zpowTwo b (trvExp τ x) := by
    intro x
    rcases hτ x with h | h
    · rw [show trvExp τ x = 0 by simp [trvExp, h], zpowTwo_zero, mul_one, h]
    · have hne : τ x ≠ x := by
        rw [h]
        intro hc
        exact hb (mul_left_cancel (by rw [mul_one]; exact hc))
      rw [show trvExp τ x = 1 by simp [trvExp, hne], zpowTwo_one, h]
  have hσbe : ∀ m : ZMod 2, σ (zpowTwo b m)
      = zpowTwo b m * zpowTwo a (trvExp σ b * m) := by
    intro m
    rcases eq_or_ne m 0 with rfl | hm
    · simp [zpowTwo_zero]
    · have hm1 : m = 1 := by
        rcases zmod2_eq_zero_or_one m with h0 | h1
        · exact absurd h0 hm
        · exact h1
      rw [hm1, mul_one, zpowTwo_one]
      exact hs b
  have hτae : ∀ m : ZMod 2, τ (zpowTwo a m)
      = zpowTwo a m * zpowTwo b (trvExp τ a * m) := by
    intro m
    rcases eq_or_ne m 0 with rfl | hm
    · simp [zpowTwo_zero]
    · have hm1 : m = 1 := by
        rcases zmod2_eq_zero_or_one m with h0 | h1
        · exact absurd h0 hm
        · exact h1
      rw [hm1, mul_one, zpowTwo_one]
      exact ht a
  have hs_mul : ∀ x (I J : ZMod 2),
      trvExp σ (x * zpowTwo a I * zpowTwo b J) = trvExp σ x + trvExp σ b * J := by
    intro x I J
    have h1 : σ (x * zpowTwo a I * zpowTwo b J)
        = (x * zpowTwo a I * zpowTwo b J)
          * zpowTwo a (trvExp σ x + trvExp σ b * J) := by
      rw [map_mul, map_mul, hσae I, hσbe J, hs x, zpowTwo_add ha2]
      ac_rfl
    have hmul : (x * zpowTwo a I * zpowTwo b J)
          * zpowTwo a (trvExp σ (x * zpowTwo a I * zpowTwo b J))
        = (x * zpowTwo a I * zpowTwo b J)
          * zpowTwo a (trvExp σ x + trvExp σ b * J) := by
      rw [← hs (x * zpowTwo a I * zpowTwo b J)]
      exact h1
    exact zpowTwo_injective ha (mul_left_cancel hmul)
  have ht_mul : ∀ x (I J : ZMod 2),
      trvExp τ (x * zpowTwo a I * zpowTwo b J) = trvExp τ x + trvExp τ a * I := by
    intro x I J
    have h1 : τ (x * zpowTwo a I * zpowTwo b J)
        = (x * zpowTwo a I * zpowTwo b J)
          * zpowTwo b (trvExp τ x + trvExp τ a * I) := by
      rw [map_mul, map_mul, hτae I, hτbe J, ht x, zpowTwo_add hb2]
      ac_rfl
    have hmul : (x * zpowTwo a I * zpowTwo b J)
          * zpowTwo b (trvExp τ (x * zpowTwo a I * zpowTwo b J))
        = (x * zpowTwo a I * zpowTwo b J)
          * zpowTwo b (trvExp τ x + trvExp τ a * I) := by
      rw [← ht (x * zpowTwo a I * zpowTwo b J)]
      exact h1
    exact zpowTwo_injective hb (mul_left_cancel hmul)
  have hstep : ∀ y, (σ * τ) y
      = y * zpowTwo a (trvExp σ y + trvExp σ b * trvExp τ y) * zpowTwo b (trvExp τ y) := by
    intro y
    rw [MulAut.mul_apply, ht y, map_mul, hσbe (trvExp τ y), hs y, zpowTwo_add ha2]
    ac_rfl
  have hs_step : ∀ x, trvExp σ ((σ * τ) x) = trvExp σ x + trvExp σ b * trvExp τ x := by
    intro x
    rw [hstep x]
    exact hs_mul x (trvExp σ x + trvExp σ b * trvExp τ x) (trvExp τ x)
  have ht_step : ∀ x, trvExp τ ((σ * τ) x)
      = trvExp τ x + trvExp τ a * (trvExp σ x + trvExp σ b * trvExp τ x) := by
    intro x
    rw [hstep x]
    exact ht_mul x (trvExp σ x + trvExp σ b * trvExp τ x) (trvExp τ x)
  have hφne : σ * τ ≠ 1 := by
    intro hφ1
    have hτσ : τ = σ := by
      ext x
      have hx : σ (τ x) = x := by
        have h0 := congrArg (fun f : MulAut E => f x) hφ1
        rwa [MulAut.mul_apply, MulAut.one_apply] at h0
      rw [← hσ2 (τ x), hx]
    have hτne : ∃ x, τ x ≠ x := by
      by_contra hc
      apply hτ1
      ext x
      by_contra hx
      exact hc ⟨x, hx⟩
    obtain ⟨x, hx⟩ := hτne
    have hτx : τ x = x * b := by
      rcases hτ x with hh | hh
      · exact absurd hh hx
      · exact hh
    have hσxb : σ x = x * b := by rw [← hτσ]; exact hτx
    have hxb : x * b ≠ x := by
      intro hh
      exact hb (mul_left_cancel (by rw [mul_one]; exact hh))
    have hσx : σ x = x * a := by
      rcases hσ x with hh | hh
      · exact absurd ((hh.symm.trans hσxb).symm) hxb
      · exact hh
    exact hab (mul_left_cancel (by rw [← hσx, hσxb]))
  have hα01 : trvExp σ b = 0 ∨ trvExp σ b = 1 := by
    by_cases h : σ b = b
    · left; simp [trvExp, h]
    · right; simp [trvExp, h]
  have hβ01 : trvExp τ a = 0 ∨ trvExp τ a = 1 := by
    by_cases h : τ a = a
    · left; simp [trvExp, h]
    · right; simp [trvExp, h]
  rcases hα01 with hα | hα <;> rcases hβ01 with hβ | hβ <;> simp only [hα, hβ] at *
  ·
    left
    have h2 : (σ * τ) ^ 2 = 1 := by
      ext x
      rw [pow_two, MulAut.mul_apply, MulAut.one_apply]
      rw [hstep ((σ * τ) x), hs_step x, ht_step x, hstep x]
      simp only [zero_mul, add_zero]
      rw [show (x * zpowTwo a (trvExp σ x) * zpowTwo b (trvExp τ x))
            * zpowTwo a (trvExp σ x) * zpowTwo b (trvExp τ x)
          = x * (zpowTwo a (trvExp σ x) * zpowTwo a (trvExp σ x))
              * (zpowTwo b (trvExp τ x) * zpowTwo b (trvExp τ x)) from by ac_rfl]
      simp only [← zpowTwo_add ha2, ← zpowTwo_add hb2]
      rw [show trvExp σ x + trvExp σ x = 0 from by ring_nf <;> simp,
        show trvExp τ x + trvExp τ x = 0 from by ring_nf <;> simp]
      simp [zpowTwo_zero]
    have hdvd : orderOf (σ * τ) ∣ 2 := orderOf_dvd_of_pow_eq_one h2
    have hne : orderOf (σ * τ) ≠ 1 := fun h => hφne (orderOf_eq_one_iff.mp h)
    rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h | h
    · exact absurd h hne
    · exact h
  ·
    have h4 : (σ * τ) ^ 4 = 1 := by
      ext x
      have hs1 : trvExp σ ((σ * τ) x) = trvExp σ x := by
        rw [hs_step x]; ring_nf <;> simp
      have ht1 : trvExp τ ((σ * τ) x) = trvExp σ x + trvExp τ x := by
        rw [ht_step x]; ring_nf <;> simp
      have hs2 : trvExp σ (((σ * τ) ^ 2) x) = trvExp σ x := by
        rw [show ((σ * τ) ^ 2) x = (σ * τ) ((σ * τ) x) from by rw [pow_two, MulAut.mul_apply]]
        rw [hs_step ((σ * τ) x), hs1, ht1]; ring_nf <;> simp
      have ht2 : trvExp τ (((σ * τ) ^ 2) x) = trvExp τ x := by
        rw [show ((σ * τ) ^ 2) x = (σ * τ) ((σ * τ) x) from by rw [pow_two, MulAut.mul_apply]]
        rw [ht_step ((σ * τ) x), hs1, ht1]; ring_nf <;> simp
      have hs3 : trvExp σ (((σ * τ) ^ 3) x) = trvExp σ x := by
        rw [show ((σ * τ) ^ 3) x = (σ * τ) (((σ * τ) ^ 2) x) from by
          rw [show (3 : ℕ) = 2 + 1 by norm_num, pow_succ', MulAut.mul_apply]]
        rw [hs_step (((σ * τ) ^ 2) x), hs2, ht2]; ring_nf <;> simp
      have ht3 : trvExp τ (((σ * τ) ^ 3) x) = trvExp σ x + trvExp τ x := by
        rw [show ((σ * τ) ^ 3) x = (σ * τ) (((σ * τ) ^ 2) x) from by
          rw [show (3 : ℕ) = 2 + 1 by norm_num, pow_succ', MulAut.mul_apply]]
        rw [ht_step (((σ * τ) ^ 2) x), hs2, ht2]; ring_nf <;> simp
      have h1 : (σ * τ) x = x * zpowTwo a (trvExp σ x) * zpowTwo b (trvExp τ x) := by
        rw [hstep x]
        rw [show trvExp σ x + 0 * trvExp τ x = trvExp σ x from by ring_nf <;> simp]
      have h2p : ((σ * τ) ^ 2) x = (σ * τ) x * zpowTwo a (trvExp σ x)
          * zpowTwo b (trvExp σ x + trvExp τ x) := by
        rw [show ((σ * τ) ^ 2) x = (σ * τ) ((σ * τ) x) from by rw [pow_two, MulAut.mul_apply]]
        rw [hstep ((σ * τ) x), hs1, ht1]
        rw [show trvExp σ x + 0 * (trvExp σ x + trvExp τ x) = trvExp σ x from by
          ring_nf <;> simp]
      have h3p : ((σ * τ) ^ 3) x = ((σ * τ) ^ 2) x * zpowTwo a (trvExp σ x)
          * zpowTwo b (trvExp τ x) := by
        rw [show ((σ * τ) ^ 3) x = (σ * τ) (((σ * τ) ^ 2) x) from by
          rw [show (3 : ℕ) = 2 + 1 by norm_num, pow_succ', MulAut.mul_apply]]
        rw [hstep (((σ * τ) ^ 2) x), hs2, ht2]
        rw [show trvExp σ x + 0 * trvExp τ x = trvExp σ x from by ring_nf <;> simp]
      have h4p : ((σ * τ) ^ 4) x = ((σ * τ) ^ 3) x * zpowTwo a (trvExp σ x)
          * zpowTwo b (trvExp σ x + trvExp τ x) := by
        rw [show ((σ * τ) ^ 4) x = (σ * τ) (((σ * τ) ^ 3) x) from by
          rw [show (4 : ℕ) = 3 + 1 by norm_num, pow_succ', MulAut.mul_apply]]
        rw [hstep (((σ * τ) ^ 3) x), hs3, ht3]
        rw [show trvExp σ x + 0 * (trvExp σ x + trvExp τ x) = trvExp σ x from by
          ring_nf <;> simp]
      rw [h4p, h3p, h2p, h1]
      rw [show ((x * zpowTwo a (trvExp σ x) * zpowTwo b (trvExp τ x))
              * zpowTwo a (trvExp σ x) * zpowTwo b (trvExp σ x + trvExp τ x))
              * zpowTwo a (trvExp σ x) * zpowTwo b (trvExp τ x)
              * zpowTwo a (trvExp σ x) * zpowTwo b (trvExp σ x + trvExp τ x)
            = x * (zpowTwo a (trvExp σ x) * zpowTwo a (trvExp σ x)
                  * zpowTwo a (trvExp σ x) * zpowTwo a (trvExp σ x))
                * (zpowTwo b (trvExp τ x) * zpowTwo b (trvExp σ x + trvExp τ x)
                  * zpowTwo b (trvExp τ x) * zpowTwo b (trvExp σ x + trvExp τ x))
            from by ac_rfl]
      rw [← zpowTwo_add ha2, ← zpowTwo_add ha2, ← zpowTwo_add ha2,
          ← zpowTwo_add hb2, ← zpowTwo_add hb2, ← zpowTwo_add hb2]
      rw [show trvExp σ x + trvExp σ x + trvExp σ x + trvExp σ x = 0 from by
            ring_nf <;> simp,
          show trvExp τ x + (trvExp σ x + trvExp τ x) + trvExp τ x
              + (trvExp σ x + trvExp τ x) = 0 from by ring_nf <;> simp]
      simp [zpowTwo_zero]
    have hdvd : orderOf (σ * τ) ∣ 4 := orderOf_dvd_of_pow_eq_one h4
    have hne : orderOf (σ * τ) ≠ 1 := fun h => hφne (orderOf_eq_one_iff.mp h)
    have h24 : orderOf (σ * τ) = 2 ∨ orderOf (σ * τ) = 4 := by
      obtain ⟨k, hk2, hk⟩ :=
        (Nat.dvd_prime_pow Nat.prime_two).mp (show orderOf (σ * τ) ∣ 2 ^ 2 by simpa using hdvd)
      interval_cases k <;> simp_all
    rcases h24 with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inr h)
  ·
    have h4 : (σ * τ) ^ 4 = 1 := by
      ext x
      have hs1 : trvExp σ ((σ * τ) x) = trvExp σ x + trvExp τ x := by
        rw [hs_step x]; ring_nf <;> simp
      have ht1 : trvExp τ ((σ * τ) x) = trvExp τ x := by
        rw [ht_step x]; ring_nf <;> simp
      have hs2 : trvExp σ (((σ * τ) ^ 2) x) = trvExp σ x := by
        rw [show ((σ * τ) ^ 2) x = (σ * τ) ((σ * τ) x) from by rw [pow_two, MulAut.mul_apply]]
        rw [hs_step ((σ * τ) x), hs1, ht1]; ring_nf <;> simp
      have ht2 : trvExp τ (((σ * τ) ^ 2) x) = trvExp τ x := by
        rw [show ((σ * τ) ^ 2) x = (σ * τ) ((σ * τ) x) from by rw [pow_two, MulAut.mul_apply]]
        rw [ht_step ((σ * τ) x), hs1, ht1]; ring_nf <;> simp
      have hs3 : trvExp σ (((σ * τ) ^ 3) x) = trvExp σ x + trvExp τ x := by
        rw [show ((σ * τ) ^ 3) x = (σ * τ) (((σ * τ) ^ 2) x) from by
          rw [show (3 : ℕ) = 2 + 1 by norm_num, pow_succ', MulAut.mul_apply]]
        rw [hs_step (((σ * τ) ^ 2) x), hs2, ht2]; ring_nf <;> simp
      have ht3 : trvExp τ (((σ * τ) ^ 3) x) = trvExp τ x := by
        rw [show ((σ * τ) ^ 3) x = (σ * τ) (((σ * τ) ^ 2) x) from by
          rw [show (3 : ℕ) = 2 + 1 by norm_num, pow_succ', MulAut.mul_apply]]
        rw [ht_step (((σ * τ) ^ 2) x), hs2, ht2]; ring_nf <;> simp
      have h1 : (σ * τ) x = x * zpowTwo a (trvExp σ x + trvExp τ x)
          * zpowTwo b (trvExp τ x) := by
        rw [hstep x]
        rw [show trvExp σ x + 1 * trvExp τ x = trvExp σ x + trvExp τ x from by ring_nf <;> simp]
      have h2p : ((σ * τ) ^ 2) x = (σ * τ) x * zpowTwo a (trvExp σ x)
          * zpowTwo b (trvExp τ x) := by
        rw [show ((σ * τ) ^ 2) x = (σ * τ) ((σ * τ) x) from by rw [pow_two, MulAut.mul_apply]]
        rw [hstep ((σ * τ) x), hs1, ht1]
        rw [show (trvExp σ x + trvExp τ x) + 1 * trvExp τ x = trvExp σ x from by
          ring_nf <;> simp]
      have h3p : ((σ * τ) ^ 3) x = ((σ * τ) ^ 2) x * zpowTwo a (trvExp σ x + trvExp τ x)
          * zpowTwo b (trvExp τ x) := by
        rw [show ((σ * τ) ^ 3) x = (σ * τ) (((σ * τ) ^ 2) x) from by
          rw [show (3 : ℕ) = 2 + 1 by norm_num, pow_succ', MulAut.mul_apply]]
        rw [hstep (((σ * τ) ^ 2) x), hs2, ht2]
        rw [show trvExp σ x + 1 * trvExp τ x = trvExp σ x + trvExp τ x from by
          ring_nf <;> simp]
      have h4p : ((σ * τ) ^ 4) x = ((σ * τ) ^ 3) x * zpowTwo a (trvExp σ x)
          * zpowTwo b (trvExp τ x) := by
        rw [show ((σ * τ) ^ 4) x = (σ * τ) (((σ * τ) ^ 3) x) from by
          rw [show (4 : ℕ) = 3 + 1 by norm_num, pow_succ', MulAut.mul_apply]]
        rw [hstep (((σ * τ) ^ 3) x), hs3, ht3]
        rw [show (trvExp σ x + trvExp τ x) + 1 * trvExp τ x = trvExp σ x from by
          ring_nf <;> simp]
      rw [h4p, h3p, h2p, h1]
      rw [show (((x * zpowTwo a (trvExp σ x + trvExp τ x) * zpowTwo b (trvExp τ x))
              * zpowTwo a (trvExp σ x) * zpowTwo b (trvExp τ x))
              * zpowTwo a (trvExp σ x + trvExp τ x) * zpowTwo b (trvExp τ x))
              * zpowTwo a (trvExp σ x) * zpowTwo b (trvExp τ x)
            = x * (zpowTwo a (trvExp σ x + trvExp τ x) * zpowTwo a (trvExp σ x)
                  * zpowTwo a (trvExp σ x + trvExp τ x) * zpowTwo a (trvExp σ x))
                * (zpowTwo b (trvExp τ x) * zpowTwo b (trvExp τ x)
                  * zpowTwo b (trvExp τ x) * zpowTwo b (trvExp τ x))
            from by ac_rfl]
      rw [← zpowTwo_add ha2, ← zpowTwo_add ha2, ← zpowTwo_add ha2,
          ← zpowTwo_add hb2, ← zpowTwo_add hb2, ← zpowTwo_add hb2]
      rw [show (trvExp σ x + trvExp τ x) + trvExp σ x + (trvExp σ x + trvExp τ x)
            + trvExp σ x = 0 from by ring_nf <;> simp,
          show trvExp τ x + trvExp τ x + trvExp τ x + trvExp τ x = 0 from by ring_nf <;> simp]
      simp [zpowTwo_zero]
    have hdvd : orderOf (σ * τ) ∣ 4 := orderOf_dvd_of_pow_eq_one h4
    have hne : orderOf (σ * τ) ≠ 1 := fun h => hφne (orderOf_eq_one_iff.mp h)
    have h24 : orderOf (σ * τ) = 2 ∨ orderOf (σ * τ) = 4 := by
      obtain ⟨k, hk2, hk⟩ :=
        (Nat.dvd_prime_pow Nat.prime_two).mp (show orderOf (σ * τ) ∣ 2 ^ 2 by simpa using hdvd)
      interval_cases k <;> simp_all
    rcases h24 with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inr h)
  ·
    right; left
    have h3 : (σ * τ) ^ 3 = 1 := by
      ext x
      have hs1 : trvExp σ ((σ * τ) x) = trvExp σ x + trvExp τ x := by
        rw [hs_step x]; ring_nf <;> simp
      have ht1 : trvExp τ ((σ * τ) x) = trvExp σ x := by
        rw [ht_step x]; ring_nf <;> simp
      have hs2 : trvExp σ (((σ * τ) ^ 2) x) = trvExp τ x := by
        rw [show ((σ * τ) ^ 2) x = (σ * τ) ((σ * τ) x) from by rw [pow_two, MulAut.mul_apply]]
        rw [hs_step ((σ * τ) x), hs1, ht1]; ring_nf <;> simp
      have ht2 : trvExp τ (((σ * τ) ^ 2) x) = trvExp σ x + trvExp τ x := by
        rw [show ((σ * τ) ^ 2) x = (σ * τ) ((σ * τ) x) from by rw [pow_two, MulAut.mul_apply]]
        rw [ht_step ((σ * τ) x), hs1, ht1]; ring_nf <;> simp
      have h1 : (σ * τ) x = x * zpowTwo a (trvExp σ x + trvExp τ x)
          * zpowTwo b (trvExp τ x) := by
        rw [hstep x]
        rw [show trvExp σ x + 1 * trvExp τ x = trvExp σ x + trvExp τ x from by ring_nf <;> simp]
      have h2p : ((σ * τ) ^ 2) x = (σ * τ) x * zpowTwo a (trvExp τ x)
          * zpowTwo b (trvExp σ x) := by
        rw [show ((σ * τ) ^ 2) x = (σ * τ) ((σ * τ) x) from by rw [pow_two, MulAut.mul_apply]]
        rw [hstep ((σ * τ) x), hs1, ht1]
        rw [show (trvExp σ x + trvExp τ x) + 1 * trvExp σ x = trvExp τ x from by
          ring_nf <;> simp]
      have h3p : ((σ * τ) ^ 3) x = ((σ * τ) ^ 2) x * zpowTwo a (trvExp σ x)
          * zpowTwo b (trvExp σ x + trvExp τ x) := by
        rw [show ((σ * τ) ^ 3) x = (σ * τ) (((σ * τ) ^ 2) x) from by
          rw [show (3 : ℕ) = 2 + 1 by norm_num, pow_succ', MulAut.mul_apply]]
        rw [hstep (((σ * τ) ^ 2) x), hs2, ht2]
        rw [show trvExp τ x + 1 * (trvExp σ x + trvExp τ x) = trvExp σ x from by
          ring_nf <;> simp]
      rw [h3p, h2p, h1]
      rw [zpowTwo_add ha2 (trvExp σ x) (trvExp τ x),
          zpowTwo_add hb2 (trvExp σ x) (trvExp τ x)]
      rw [show ((x * (zpowTwo a (trvExp σ x) * zpowTwo a (trvExp τ x))
              * zpowTwo b (trvExp τ x)) * zpowTwo a (trvExp τ x)
              * zpowTwo b (trvExp σ x)) * zpowTwo a (trvExp σ x)
              * (zpowTwo b (trvExp σ x) * zpowTwo b (trvExp τ x))
            = x * (zpowTwo a (trvExp σ x) * zpowTwo a (trvExp σ x))
                * (zpowTwo a (trvExp τ x) * zpowTwo a (trvExp τ x))
                * (zpowTwo b (trvExp τ x) * zpowTwo b (trvExp τ x))
                * (zpowTwo b (trvExp σ x) * zpowTwo b (trvExp σ x)) from by ac_rfl]
      simp only [← zpowTwo_add ha2, ← zpowTwo_add hb2]
      rw [show trvExp σ x + trvExp σ x = 0 from by ring_nf <;> simp,
          show trvExp τ x + trvExp τ x = 0 from by ring_nf <;> simp]
      simp [zpowTwo_zero]
    have hdvd : orderOf (σ * τ) ∣ 3 := orderOf_dvd_of_pow_eq_one h3
    have hne : orderOf (σ * τ) ≠ 1 := fun h => hφne (orderOf_eq_one_iff.mp h)
    rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h | h
    · exact absurd h hne
    · exact h

theorem s16c1_G47_two_le_card_fixed {G : Type*} [Group G] [Finite G] {S V₀ : Subgroup G}
    (hS : IsPGroup 2 S) (hSN : S ≤ normalizer (V₀ : Set G)) (hV₀ : IsPGroup 2 V₀)
    (hcard : Nat.card V₀ ≤ 4) :
    Nat.card V₀ ≤ 2 * Nat.card ↥(V₀ ⊓ centralizer (S : Set G)) := by
  haveI : Fact (Nat.Prime 2) := Fact.mk Nat.prime_two
  haveI : Subgroup.Normalizes S V₀ := ⟨hSN⟩
  have hsmul : ∀ (s : ↥S) (v : ↥V₀),
      ((s • v : ↥V₀) : G) = (s : G) * (v : G) * (s : G)⁻¹ :=
    fun s v => Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe S V₀ s v
  haveI : Nonempty ↥(V₀ ⊓ centralizer (S : Set G)) := ⟨⟨1, by simp⟩⟩
  let e : ↥(V₀ ⊓ centralizer (S : Set G)) ≃ ↥(MulAction.fixedPoints ↥S ↥V₀) :=
  { toFun := fun x =>
      ⟨⟨x.1, x.2.1⟩, by
        intro s
        apply Subtype.ext
        rw [hsmul, mul_inv_eq_iff_eq_mul]
        exact (Subgroup.mem_centralizer_iff.mp x.2.2) (s : G) s.2⟩
    invFun := fun y =>
      ⟨y.1.1, y.1.2, Subgroup.mem_centralizer_iff.mpr (by
        intro s hs
        have hy : (s : G) * (y.1.1) * (s : G)⁻¹ = y.1.1 := by
          simpa only [hsmul] using congrArg Subtype.val (y.2 ⟨s, hs⟩)
        rwa [mul_inv_eq_iff_eq_mul] at hy)⟩
    left_inv := fun x => by apply Subtype.ext; rfl
    right_inv := fun y => by apply Subtype.ext; apply Subtype.ext; rfl }
  have hcard_fixed : Nat.card ↥(MulAction.fixedPoints ↥S ↥V₀)
      = Nat.card ↥(V₀ ⊓ centralizer (S : Set G)) := (Nat.card_congr e).symm
  set f := Nat.card ↥(V₀ ⊓ centralizer (S : Set G)) with hf
  have hf1 : 1 ≤ f := by rw [hf]; exact Nat.card_pos
  have hmod : Nat.card ↥V₀ ≡ f [MOD 2] := by
    have h := hS.card_modEq_card_fixedPoints ↥V₀
    rwa [hcard_fixed] at h
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hV₀
  have hpow : 2 ^ n ≤ 4 := by rw [← hn]; exact hcard
  have hn2 : n ≤ 2 := by
    have h : 2 ^ n < 2 ^ 3 := lt_of_le_of_lt hpow (by norm_num)
    exact Nat.lt_succ_iff.mp ((Nat.pow_lt_pow_iff_right (by norm_num : 1 < 2)).mp h)
  rw [hn]
  interval_cases n
  · simp; omega
  · simp; omega
  · have hfmod : f % 2 = 0 := by
      have h := hmod
      rw [Nat.ModEq] at h
      norm_num at h
      omega
    have h2f : 2 ≤ f := Nat.le_of_dvd (by omega) (Nat.dvd_of_mod_eq_zero hfmod)
    omega

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
