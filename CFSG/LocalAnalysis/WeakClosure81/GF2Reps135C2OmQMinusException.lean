module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2OmQMinusExcPoints
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2OmQMinusExcArith

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.StandardType

private lemma c2slomqmex_pow_ne_zero {m : ℕ} (hm_odd : Odd m) (hm_gt : 1 < m) (u : ℕ) :
    (((2 ^ u : ℕ) : ZMod m)) ≠ 0 := by
  haveI : Fact (1 < m) := ⟨hm_gt⟩
  have hcop : Nat.Coprime (2 ^ u) m := Nat.Coprime.pow_left u hm_odd.coprime_two_left
  exact ((ZMod.isUnit_iff_coprime (2 ^ u) m).mpr hcop).ne_zero

private lemma c2slomqmex_digit_le {C u : ℕ} (h : Odd (Nat.choose C (2 ^ u))) :
    2 ^ u ≤ C := by
  by_contra hle
  have hlt : C < 2 ^ u := not_le.1 hle
  rw [Nat.choose_eq_zero_of_lt hlt] at h
  obtain ⟨k, hk⟩ := h
  omega

theorem omq_minus_exists_exception_weights {f : ℕ} (hf : 2 ≤ f) {m h : ℕ} (hm : m = 2 ^ f - 1)
    (hh : h = 2 ^ f + 1) {a : ZMod m} {d : ZMod h} {C : ℕ} (hC1 : 1 ≤ C) (hCQ : C < m * h)
    (hpow : ∀ u : ℕ, C ≠ 2 ^ u) (hCa : (C : ZMod m) = 2 * a) (hCd : (C : ZMod h) = 2 * d)
    {π : Equiv.Perm (Fin 3)} {s : Fin 3 → ℤ}
    (hA : (∀ c, s c = 1) ∧ π * π = 1 ∧ π 0 = 1 ∧ π 1 = 0) :
    ∃ j : ℕ, 0 < j ∧ j < C ∧ Odd (Nat.choose C j) ∧
      ∃ u : Fin 4 → OmqMinusLat 3 m h, Function.Injective u ∧
        (∀ i, OmqMinusInOrbit
          ((((![a - (j : ZMod m), a, a] : Fin 3 → ZMod m)), d - (j : ZMod h)) :
            OmqMinusLat 3 m h) (u i)) ∧
        ∀ i i', u i ≠ omqMinusAct π s (u i') := by
  have hf_ne : f ≠ 0 := by omega
  have heven : Even (2 ^ f) := Even.pow_of_ne_zero even_two hf_ne
  have h2f_ge : 4 ≤ 2 ^ f := by
    have hle : 2 ^ 2 ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
    simpa using hle
  have hm_odd : Odd m := by
    rw [hm]
    exact Nat.Even.sub_odd (by omega : 1 ≤ 2 ^ f) heven odd_one
  have hh_odd : Odd h := by
    rw [hh]
    exact heven.add_one
  have hm_gt : 1 < m := by rw [hm]; omega
  obtain ⟨⟨u₁, hu₁odd, hu₁ne⟩, hdig⟩ := omq_minus_exists_digit hf hm hh hC1 hCQ hpow
  by_cases ha0 : a = 0
  · subst ha0
    obtain ⟨v, hvodd, hvne⟩ := hdig d
    refine ⟨2 ^ v, pow_pos (by norm_num) v, ?_, hvodd, ?_⟩
    · have hle : 2 ^ v ≤ C := c2slomqmex_digit_le hvodd
      exact lt_of_le_of_ne hle (Ne.symm (hpow v))
    · have hp : -(((2 ^ v : ℕ) : ZMod m)) ≠ 0 :=
        neg_ne_zero.mpr (c2slomqmex_pow_ne_zero hm_odd hm_gt v)
      have he : d - ((2 ^ v : ℕ) : ZMod h) ≠ 0 := by
        intro hzero
        exact hvne (sub_eq_zero.mp hzero).symm
      simp only [zero_sub]
      exact omq_minus_exists_exc_points_single hm_odd hh_odd hp he hA
  · refine ⟨2 ^ u₁, pow_pos (by norm_num) u₁, ?_, hu₁odd, ?_⟩
    · have hle : 2 ^ u₁ ≤ C := c2slomqmex_digit_le hu₁odd
      exact lt_of_le_of_ne hle (Ne.symm (hpow u₁))
    · have hjne : (((2 ^ u₁ : ℕ) : ZMod m)) ≠ 0 := c2slomqmex_pow_ne_zero hm_odd hm_gt u₁
      have hb : a - ((2 ^ u₁ : ℕ) : ZMod m) ≠ a := by
        intro heq
        exact hjne (by linear_combination -heq)
      have hbna : a - ((2 ^ u₁ : ℕ) : ZMod m) ≠ -a := by
        intro heq
        have h2 : (((2 ^ u₁ : ℕ) : ZMod m)) = 2 * a := by linear_combination -heq
        exact hu₁ne (h2.trans hCa.symm)
      exact omq_minus_exists_exc_points_ne hm_odd ha0 hb hbna
        (d - ((2 ^ u₁ : ℕ) : ZMod h)) hA

end CFSG.LocalAnalysis.WeakClosure81
