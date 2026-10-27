module

public import CFSG.RepresentationTheory.SzMartineau.TwoPowMod
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Data.Fin.VecNotation

public section

namespace CFSG.RepresentationTheory.SzMartineau

@[expose] def IsTwoPow (a : ℕ) (w : ZMod (2 ^ (2 * a + 1) - 1)) : Prop := ∃ k : ℕ, w = 2 ^ k

@[expose] def szWt (a : ℕ) : Fin 4 → ZMod (2 ^ (2 * a + 1) - 1) :=
  ![1 + 2 ^ a, 2 ^ a, -2 ^ a, -(1 + 2 ^ a)]

@[expose] def posWt (a c : ℕ) (i j : Fin 4) : ZMod (2 ^ (2 * a + 1) - 1) :=
  szWt a i - 2 ^ c * szWt a j

private lemma posWt_two_zero (a c : ℕ) :
    posWt a c 2 0 = -((2 : ZMod (2 ^ (2 * a + 1) - 1)) ^ a + 2 ^ c + 2 ^ (a + c)) := by
  simp [posWt, szWt]
  ring

private lemma posWt_two_one (a c : ℕ) :
    posWt a c 2 1 = -((2 : ZMod (2 ^ (2 * a + 1) - 1)) ^ a + 2 ^ (a + c)) := by
  simp [posWt, szWt]
  ring

private lemma posWt_one_zero_add_three_two (a c : ℕ) :
    posWt a c 1 0 + posWt a c 3 2 =
      -(1 + (2 : ZMod (2 ^ (2 * a + 1) - 1)) ^ c) := by
  simp [posWt, szWt]
  ring

private lemma posWt_zero_one_add_two_three (a c : ℕ) :
    posWt a c 0 1 + posWt a c 2 3 =
      1 + (2 : ZMod (2 ^ (2 * a + 1) - 1)) ^ c := by
  simp [posWt, szWt]
  ring

private lemma posWt_zero_zero (a c : ℕ) :
    posWt a c 0 0 =
      (1 + (2 : ZMod (2 ^ (2 * a + 1) - 1)) ^ a) * (1 - 2 ^ c) := by
  simp [posWt, szWt]
  ring

private lemma posWt_one_one (a c : ℕ) :
    posWt a c 1 1 = (2 : ZMod (2 ^ (2 * a + 1) - 1)) ^ a * (1 - 2 ^ c) := by
  simp [posWt, szWt]
  ring

private lemma posWt_two_two (a c : ℕ) :
    posWt a c 2 2 = (2 : ZMod (2 ^ (2 * a + 1) - 1)) ^ a * (2 ^ c - 1) := by
  simp [posWt, szWt]
  ring

private lemma posWt_three_three (a c : ℕ) :
    posWt a c 3 3 =
      (1 + (2 : ZMod (2 ^ (2 * a + 1) - 1)) ^ a) * (2 ^ c - 1) := by
  simp [posWt, szWt]
  ring

private lemma posWt_zero_one (a c : ℕ) :
    posWt a c 0 1 =
      1 + (2 : ZMod (2 ^ (2 * a + 1) - 1)) ^ a - 2 ^ (a + c) := by
  simp [posWt, szWt]
  ring

private lemma two_pow_mul_two_pow_succ (a : ℕ) :
    (2 : ZMod (2 ^ (2 * a + 1) - 1)) ^ a * 2 ^ (a + 1) = 1 := by
  have h : a + (a + 1) = 2 * a + 1 := by omega
  calc
    (2 : ZMod (2 ^ (2 * a + 1) - 1)) ^ a * 2 ^ (a + 1) =
        2 ^ (a + (a + 1)) := (pow_add _ _ _).symm
    _ = 1 := by rw [h, two_pow_self_eq_one]

private lemma one_add_two_pow_mul_inv (a : ℕ) :
    (1 + (2 : ZMod (2 ^ (2 * a + 1) - 1)) ^ a) * (2 - 2 ^ (a + 1)) = 1 := by
  have hpow : (2 : ZMod (2 ^ (2 * a + 1) - 1)) ^ (2 * a + 1) = 1 :=
    two_pow_self_eq_one (2 * a + 1)
  have hs : (2 : ZMod (2 ^ (2 * a + 1) - 1)) ^ (a + 1) =
      (2 : ZMod (2 ^ (2 * a + 1) - 1)) ^ a * 2 := pow_succ _ _
  have hsq : (2 : ZMod (2 ^ (2 * a + 1) - 1)) ^ (2 * a + 1) =
      ((2 : ZMod (2 ^ (2 * a + 1) - 1)) ^ a * 2 ^ a) * 2 := by
    calc
      (2 : ZMod (2 ^ (2 * a + 1) - 1)) ^ (2 * a + 1) =
          2 ^ ((a + a) + 1) := by rw [show 2 * a + 1 = (a + a) + 1 by omega]
      _ = 2 ^ (a + a) * 2 ^ 1 := pow_add _ _ _
      _ = 2 ^ (a + a) * 2 := by rw [pow_one]
      _ = ((2 : ZMod (2 ^ (2 * a + 1) - 1)) ^ a * 2 ^ a) * 2 := by
            exact congrArg (· * 2) (pow_add _ _ _)
  have hr2 : (2 : ZMod (2 ^ (2 * a + 1) - 1)) ^ a * 2 ^ a * 2 = 1 :=
    hsq.symm.trans hpow
  calc
    (1 + (2 : ZMod (2 ^ (2 * a + 1) - 1)) ^ a) * (2 - 2 ^ (a + 1))
        = 2 - ((2 : ZMod (2 ^ (2 * a + 1) - 1)) ^ a *
            2 ^ a) * 2 := by
          rw [hs]
          ring
    _ = 2 - 1 := by rw [hr2]
    _ = 1 := by ring

theorem not_isTwoPow_posWt_two_zero {a : ℕ} (ha : 2 ≤ a) (c : ℕ) :
    ¬ IsTwoPow a (posWt a c 2 0) := by
  rintro ⟨k, hk⟩
  have hf : 4 < 2 * a + 1 := by omega
  rw [posWt_two_zero] at hk
  have hzero : (2 : ZMod (2 ^ (2 * a + 1) - 1)) ^ a + 2 ^ c + 2 ^ (a + c) +
      2 ^ k = 0 := by
    linear_combination -hk
  have hlist : (([a, c, a + c, k].map fun u =>
      (2 : ZMod (2 ^ (2 * a + 1) - 1)) ^ u)).sum = 0 := by
    simpa [List.sum_cons, add_assoc] using hzero
  exact sum_two_pow_ne_zero (l := [a, c, a + c, k]) (by simp) (by simpa using hf) hlist

theorem not_isTwoPow_posWt_two_one {a : ℕ} (ha : 2 ≤ a) (c : ℕ) :
    ¬ IsTwoPow a (posWt a c 2 1) := by
  rintro ⟨k, hk⟩
  have hf : 3 < 2 * a + 1 := by omega
  rw [posWt_two_one] at hk
  have hzero : (2 : ZMod (2 ^ (2 * a + 1) - 1)) ^ a + 2 ^ (a + c) + 2 ^ k = 0 := by
    linear_combination -hk
  have hlist : (([a, a + c, k].map fun u =>
      (2 : ZMod (2 ^ (2 * a + 1) - 1)) ^ u)).sum = 0 := by
    simpa [List.sum_cons, add_assoc] using hzero
  exact sum_two_pow_ne_zero (l := [a, a + c, k]) (by simp) (by simpa using hf) hlist

theorem not_isTwoPow_posWt_one_zero_and_three_two {a : ℕ} (ha : 2 ≤ a) (c : ℕ) :
    ¬ (IsTwoPow a (posWt a c 1 0) ∧ IsTwoPow a (posWt a c 3 2)) := by
  rintro ⟨⟨k, hk⟩, ⟨l, hl⟩⟩
  have hf : 4 < 2 * a + 1 := by omega
  have hsum : (2 : ZMod (2 ^ (2 * a + 1) - 1)) ^ k + 2 ^ l =
      -(1 + (2 : ZMod (2 ^ (2 * a + 1) - 1)) ^ c) := by
    rw [← hk, ← hl, posWt_one_zero_add_three_two]
  have hzero : (2 : ZMod (2 ^ (2 * a + 1) - 1)) ^ k + 2 ^ l + 1 + 2 ^ c = 0 := by
    linear_combination hsum
  have hlist : (([k, l, 0, c].map fun u =>
      (2 : ZMod (2 ^ (2 * a + 1) - 1)) ^ u)).sum = 0 := by
    simpa [List.sum_cons, add_assoc] using hzero
  exact sum_two_pow_ne_zero (l := [k, l, 0, c]) (by simp) (by simpa using hf) hlist

private lemma mod_add_one_eq_of_add_eq_zero {f k a : ℕ} (hf : f = 2 * a + 1)
    (ha : 1 ≤ a) (h : (k + a + 1) % f = 0) : (k + 1) % f = a + 1 := by
  have hlt : a + 1 < f := by omega
  have h1 : (k + 1) + a ≡ (a + 1) + a [MOD f] := by
    rw [Nat.ModEq]
    rw [show k + 1 + a = k + a + 1 by omega, show a + 1 + a = f by omega]
    rw [h, Nat.mod_self]
  have h2 : k + 1 ≡ a + 1 [MOD f] := Nat.ModEq.add_right_cancel' a h1
  simpa [Nat.ModEq, Nat.mod_eq_of_lt hlt] using h2

private lemma mod_eq_of_add_eq_zero_and_eq {f k a c : ℕ} (hf : f = 2 * a + 1)
    (h1 : (k + 1) % f = 0) (h2 : (k + a + 1) % f = c % f) : c % f = a := by
  have hlt : a < f := by omega
  have h : (k + a + 1) % f = a := by
    calc
      (k + a + 1) % f = ((k + 1) + a) % f := by rw [show k + a + 1 = k + 1 + a by omega]
      _ = ((k + 1) % f + a % f) % f := Nat.add_mod _ _ _
      _ = (0 + a % f) % f := by rw [h1]
      _ = a := by rw [Nat.zero_add, Nat.mod_mod, Nat.mod_eq_of_lt hlt]
  rw [← h2, h]

private lemma false_of_add_eq {f k a : ℕ} (hf : f = 2 * a + 1) (ha : 2 ≤ a)
    (h : (k + a + 1) % f = (k + 1) % f) : False := by
  have h1 : (k + 1) + a ≡ (k + 1) + 0 [MOD f] := by
    rw [Nat.ModEq, Nat.add_zero]
    rw [show k + 1 + a = k + a + 1 by omega]
    exact h
  have ha0 : a ≡ 0 [MOD f] := Nat.ModEq.add_left_cancel' (k + 1) h1
  have hlt : a < f := by omega
  rw [Nat.ModEq, Nat.mod_eq_of_lt hlt, Nat.zero_mod] at ha0
  omega

theorem mod_eq_of_isTwoPow_posWt_zero_zero {a : ℕ} (ha : 2 ≤ a) {c : ℕ}
    (h : IsTwoPow a (posWt a c 0 0)) : c % (2 * a + 1) = a := by
  obtain ⟨k, hk⟩ := h
  have hf : 3 ≤ 2 * a + 1 := by omega
  have hf2 : 2 ≤ 2 * a + 1 := by omega
  rw [posWt_zero_zero] at hk
  have h1 : 1 - (2 : ZMod (2 ^ (2 * a + 1) - 1)) ^ c =
      (2 - 2 ^ (a + 1)) * 2 ^ k := by
    calc
      1 - (2 : ZMod (2 ^ (2 * a + 1) - 1)) ^ c =
          ((1 + 2 ^ a) * (2 - 2 ^ (a + 1))) * (1 - 2 ^ c) := by
            rw [one_add_two_pow_mul_inv, one_mul]
      _ = (2 - 2 ^ (a + 1)) * ((1 + 2 ^ a) * (1 - 2 ^ c)) := by ring
      _ = (2 - 2 ^ (a + 1)) * 2 ^ k := by rw [hk]
  have h1' : 1 - (2 : ZMod (2 ^ (2 * a + 1) - 1)) ^ c =
      2 ^ (k + 1) - 2 ^ (k + a + 1) := by
    rw [h1, sub_mul]
    have hfirst : (2 : ZMod (2 ^ (2 * a + 1) - 1)) * 2 ^ k = 2 ^ (k + 1) :=
      (pow_succ' _ _).symm
    have hsecond : (2 : ZMod (2 ^ (2 * a + 1) - 1)) ^ (a + 1) * 2 ^ k =
        2 ^ (k + a + 1) := by
      calc
        (2 : ZMod (2 ^ (2 * a + 1) - 1)) ^ (a + 1) * 2 ^ k =
            2 ^ ((a + 1) + k) := (pow_add _ _ _).symm
        _ = 2 ^ (k + a + 1) := by rw [show (a + 1) + k = k + a + 1 by omega]
    linear_combination hfirst - hsecond
  have h2 : (2 : ZMod (2 ^ (2 * a + 1) - 1)) ^ 0 + 2 ^ (k + a + 1) =
      2 ^ c + 2 ^ (k + 1) := by
    rw [pow_zero]
    linear_combination h1'
  have hpair := two_pow_add_two_pow_eq_two_pow_add_two_pow (f := 2 * a + 1) hf h2
  rcases hpair with ⟨_, hba⟩ | ⟨hk0, hca⟩
  · exact False.elim (false_of_add_eq (by omega) ha hba)
  · have hk0' : (k + 1) % (2 * a + 1) = 0 := by simpa using hk0.symm
    have hka : (k + a + 1) % (2 * a + 1) = c % (2 * a + 1) := hca
    exact mod_eq_of_add_eq_zero_and_eq (by omega) hk0' hka

theorem mod_eq_of_isTwoPow_posWt_one_one {a : ℕ} (ha : 2 ≤ a) {c : ℕ}
    (h : IsTwoPow a (posWt a c 1 1)) : c % (2 * a + 1) = 2 * a := by
  obtain ⟨k, hk⟩ := h
  have hf : 3 ≤ 2 * a + 1 := by omega
  rw [posWt_one_one] at hk
  have h1 : 1 - (2 : ZMod (2 ^ (2 * a + 1) - 1)) ^ c = 2 ^ (k + a + 1) := by
    calc
      1 - (2 : ZMod (2 ^ (2 * a + 1) - 1)) ^ c =
          (2 ^ a * 2 ^ (a + 1)) * (1 - 2 ^ c) := by
            rw [two_pow_mul_two_pow_succ, one_mul]
      _ = 2 ^ (a + 1) * (2 ^ a * (1 - 2 ^ c)) := by ring
      _ = 2 ^ (a + 1) * 2 ^ k := by rw [hk]
      _ = 2 ^ (k + a + 1) := by
        calc
          (2 : ZMod (2 ^ (2 * a + 1) - 1)) ^ (a + 1) * 2 ^ k =
              2 ^ ((a + 1) + k) := (pow_add _ _ _).symm
          _ = 2 ^ (k + a + 1) := by rw [show (a + 1) + k = k + a + 1 by omega]
  have h2 : (2 : ZMod (2 ^ (2 * a + 1) - 1)) ^ c + 2 ^ (k + a + 1) = 2 ^ 0 := by
    rw [pow_zero]
    linear_combination -h1
  have hs := two_pow_add_two_pow_eq_two_pow (f := 2 * a + 1) hf h2
  have hc1 : (c + 1) % (2 * a + 1) = 0 := by simpa using hs.2.symm
  have hc_mod : c + 1 ≡ 2 * a + 1 [MOD 2 * a + 1] := by
    rw [Nat.ModEq]
    have hzero : (2 * a + 1) % (2 * a + 1) = 0 := Nat.mod_self _
    rw [hzero]
    exact hc1
  have hc2 : c ≡ 2 * a [MOD 2 * a + 1] := Nat.ModEq.add_right_cancel' 1 hc_mod
  have hlt : 2 * a < 2 * a + 1 := by omega
  simpa [Nat.ModEq, Nat.mod_eq_of_lt hlt] using hc2

theorem mod_eq_of_isTwoPow_posWt_two_two {a : ℕ} (ha : 2 ≤ a) {c : ℕ}
    (h : IsTwoPow a (posWt a c 2 2)) : c % (2 * a + 1) = 1 := by
  obtain ⟨k, hk⟩ := h
  have hf : 3 ≤ 2 * a + 1 := by omega
  rw [posWt_two_two] at hk
  have h1 : (2 : ZMod (2 ^ (2 * a + 1) - 1)) ^ c - 1 = 2 ^ (k + a + 1) := by
    calc
      (2 : ZMod (2 ^ (2 * a + 1) - 1)) ^ c - 1 =
          (2 ^ a * 2 ^ (a + 1)) * (2 ^ c - 1) := by
        rw [two_pow_mul_two_pow_succ, one_mul]
      _ = 2 ^ (a + 1) * (2 ^ a * (2 ^ c - 1)) := by ring
      _ = 2 ^ (a + 1) * 2 ^ k := by rw [hk]
      _ = 2 ^ (k + a + 1) := by
        calc
          (2 : ZMod (2 ^ (2 * a + 1) - 1)) ^ (a + 1) * 2 ^ k =
              2 ^ ((a + 1) + k) := (pow_add _ _ _).symm
          _ = 2 ^ (k + a + 1) := by rw [show (a + 1) + k = k + a + 1 by omega]
  have hc : (2 : ZMod (2 ^ (2 * a + 1) - 1)) ^ c = 1 + 2 ^ (k + a + 1) := by
    linear_combination h1
  have h2 : (2 : ZMod (2 ^ (2 * a + 1) - 1)) ^ 0 + 2 ^ (k + a + 1) = 2 ^ c := by
    rw [pow_zero, hc]
  have hs := two_pow_add_two_pow_eq_two_pow (f := 2 * a + 1) hf h2
  simpa [Nat.mod_eq_of_lt (by omega : 1 < 2 * a + 1)] using hs.2

theorem mod_eq_of_isTwoPow_posWt_three_three {a : ℕ} (ha : 2 ≤ a) {c : ℕ}
    (h : IsTwoPow a (posWt a c 3 3)) : c % (2 * a + 1) = a + 1 := by
  obtain ⟨k, hk⟩ := h
  have hf : 3 ≤ 2 * a + 1 := by omega
  rw [posWt_three_three] at hk
  have h1 : (2 : ZMod (2 ^ (2 * a + 1) - 1)) ^ c - 1 =
      (2 - 2 ^ (a + 1)) * 2 ^ k := by
    calc
      (2 : ZMod (2 ^ (2 * a + 1) - 1)) ^ c - 1 =
          ((1 + 2 ^ a) * (2 - 2 ^ (a + 1))) * (2 ^ c - 1) := by
        rw [one_add_two_pow_mul_inv, one_mul]
      _ = (2 - 2 ^ (a + 1)) * ((1 + 2 ^ a) * (2 ^ c - 1)) := by ring
      _ = (2 - 2 ^ (a + 1)) * 2 ^ k := by
        simpa using congrArg (fun x => (2 - 2 ^ (a + 1)) * x) hk
  have h1' : (2 : ZMod (2 ^ (2 * a + 1) - 1)) ^ c - 1 =
      2 ^ (k + 1) - 2 ^ (k + a + 1) := by
    rw [h1, sub_mul]
    have hfirst : (2 : ZMod (2 ^ (2 * a + 1) - 1)) * 2 ^ k = 2 ^ (k + 1) :=
      (pow_succ' _ _).symm
    have hsecond : (2 : ZMod (2 ^ (2 * a + 1) - 1)) ^ (a + 1) * 2 ^ k =
        2 ^ (k + a + 1) := by
      calc
        (2 : ZMod (2 ^ (2 * a + 1) - 1)) ^ (a + 1) * 2 ^ k =
            2 ^ ((a + 1) + k) := (pow_add _ _ _).symm
        _ = 2 ^ (k + a + 1) := by rw [show (a + 1) + k = k + a + 1 by omega]
    linear_combination hfirst - hsecond
  have hc : (2 : ZMod (2 ^ (2 * a + 1) - 1)) ^ c =
      1 + 2 ^ (k + 1) - 2 ^ (k + a + 1) := by
    linear_combination h1'
  have h2 : (2 : ZMod (2 ^ (2 * a + 1) - 1)) ^ 0 + 2 ^ (k + 1) =
      2 ^ c + 2 ^ (k + a + 1) := by
    rw [pow_zero, hc]
    ring
  have hpair := two_pow_add_two_pow_eq_two_pow_add_two_pow (f := 2 * a + 1) hf h2
  rcases hpair with ⟨-, hba⟩ | ⟨hka0, hck⟩
  · exact False.elim (false_of_add_eq (by omega) ha hba.symm)
  · have hka0' : (k + a + 1) % (2 * a + 1) = 0 := by simpa using hka0.symm
    have hk1 : (k + 1) % (2 * a + 1) = a + 1 :=
      mod_add_one_eq_of_add_eq_zero (by omega) (by omega) hka0'
    rw [← hck, hk1]

private lemma mod_eq_zero_of_posWt_zero_one_eq_two_pow {a c k : ℕ} (ha : 2 ≤ a)
    (hk : posWt a c 0 1 = (2 : ZMod (2 ^ (2 * a + 1) - 1)) ^ k)
    (hkm : k % (2 * a + 1) = 0 ∨ k % (2 * a + 1) = c % (2 * a + 1)) :
    c % (2 * a + 1) = 0 := by
  have hf2 : 2 ≤ 2 * a + 1 := by omega
  rcases hkm with hk0 | hkc
  · have hk1' : (2 : ZMod (2 ^ (2 * a + 1) - 1)) ^ k =
        (2 : ZMod (2 ^ (2 * a + 1) - 1)) ^ 0 := by
      rw [two_pow_eq_two_pow_iff hf2]
      simpa using hk0
    have hk1 : (2 : ZMod (2 ^ (2 * a + 1) - 1)) ^ k = 1 := by simpa using hk1'
    have h1 : posWt a c 0 1 = 1 := by rw [hk, hk1]
    rw [posWt_zero_one] at h1
    have hr : (2 : ZMod (2 ^ (2 * a + 1) - 1)) ^ a = 2 ^ (a + c) := by
      linear_combination h1
    have hmod := (two_pow_eq_two_pow_iff hf2).mp hr
    have hcong : a + c ≡ a + 0 [MOD 2 * a + 1] := by
      rw [Nat.ModEq, Nat.add_zero]
      exact hmod.symm
    have hc0 : c ≡ 0 [MOD 2 * a + 1] := Nat.ModEq.add_left_cancel' a hcong
    simpa [Nat.ModEq] using hc0
  · have hk2 : (2 : ZMod (2 ^ (2 * a + 1) - 1)) ^ k = 2 ^ c := by
      rw [two_pow_eq_two_pow_iff hf2]
      exact hkc
    have h2 : posWt a c 0 1 = 2 ^ c := by rw [hk, hk2]
    rw [posWt_zero_one] at h2
    have hfac : 1 + (2 : ZMod (2 ^ (2 * a + 1) - 1)) ^ a =
        2 ^ c * (1 + (2 : ZMod (2 ^ (2 * a + 1) - 1)) ^ a) := by
      calc
        1 + (2 : ZMod (2 ^ (2 * a + 1) - 1)) ^ a = 2 ^ c + 2 ^ (a + c) := by
          linear_combination h2
        _ = 2 ^ c * (1 + (2 : ZMod (2 ^ (2 * a + 1) - 1)) ^ a) := by
          have hp : (2 : ZMod (2 ^ (2 * a + 1) - 1)) ^ (a + c) = 2 ^ c * 2 ^ a := by
            calc
              (2 : ZMod (2 ^ (2 * a + 1) - 1)) ^ (a + c) = 2 ^ (c + a) := by
                rw [show a + c = c + a by omega]
              _ = 2 ^ c * 2 ^ a := pow_add _ _ _
          rw [hp]
          ring
    have h1 : (1 : ZMod (2 ^ (2 * a + 1) - 1)) = 2 ^ c := by
      calc
        (1 : ZMod (2 ^ (2 * a + 1) - 1)) =
            (1 + 2 ^ a) * (2 - 2 ^ (a + 1)) := by rw [one_add_two_pow_mul_inv]
        _ = (2 ^ c * (1 + 2 ^ a)) * (2 - 2 ^ (a + 1)) := by
          exact congrArg (fun x => x * (2 - 2 ^ (a + 1))) hfac
        _ = 2 ^ c * ((1 + 2 ^ a) * (2 - 2 ^ (a + 1))) := by ring
        _ = 2 ^ c := by rw [one_add_two_pow_mul_inv, mul_one]
    have h2' : (2 : ZMod (2 ^ (2 * a + 1) - 1)) ^ c = 2 ^ 0 := by
      rw [pow_zero]
      exact h1.symm
    have hc0 := (two_pow_eq_two_pow_iff hf2).mp h2'
    simpa using hc0

theorem not_isTwoPow_posWt_zero_one_and_two_three {a : ℕ} (ha : 2 ≤ a) {c : ℕ}
    (hc : c % (2 * a + 1) ≠ 0) :
    ¬ (IsTwoPow a (posWt a c 0 1) ∧ IsTwoPow a (posWt a c 2 3)) := by
  rintro ⟨⟨k, hk⟩, ⟨l, hl⟩⟩
  have hf : 3 ≤ 2 * a + 1 := by omega
  have hsum : (2 : ZMod (2 ^ (2 * a + 1) - 1)) ^ k + 2 ^ l = 1 + 2 ^ c := by
    calc
      (2 : ZMod (2 ^ (2 * a + 1) - 1)) ^ k + 2 ^ l =
          posWt a c 0 1 + posWt a c 2 3 := by rw [← hk, ← hl]
      _ = 1 + (2 : ZMod (2 ^ (2 * a + 1) - 1)) ^ c :=
        posWt_zero_one_add_two_three a c
  have hsum' : (2 : ZMod (2 ^ (2 * a + 1) - 1)) ^ 0 + 2 ^ c = 2 ^ k + 2 ^ l := by
    rw [pow_zero]
    exact hsum.symm
  have hpair := two_pow_add_two_pow_eq_two_pow_add_two_pow (f := 2 * a + 1) hf hsum'
  have hkm : k % (2 * a + 1) = 0 ∨ k % (2 * a + 1) = c % (2 * a + 1) := by
    rcases hpair with ⟨h0k, _⟩ | ⟨_, hck⟩
    · left
      simpa using h0k.symm
    · right
      exact hck.symm
  exact hc (mod_eq_zero_of_posWt_zero_one_eq_two_pow ha hk hkm)

private lemma diag_mod_eq {a c : ℕ} (ha : 2 ≤ a) {i : Fin 4}
    (h : IsTwoPow a (posWt a c i i)) :
    c % (2 * a + 1) = match i with
      | 0 => a
      | 1 => 2 * a
      | 2 => 1
      | 3 => a + 1 := by
  fin_cases i
  · simpa using mod_eq_of_isTwoPow_posWt_zero_zero ha h
  · simpa using mod_eq_of_isTwoPow_posWt_one_one ha h
  · simpa using mod_eq_of_isTwoPow_posWt_two_two ha h
  · simpa using mod_eq_of_isTwoPow_posWt_three_three ha h

theorem diag_isTwoPow_unique {a : ℕ} (ha : 2 ≤ a) (c : ℕ) {i j : Fin 4} (hij : i ≠ j)
    (hi : IsTwoPow a (posWt a c i i)) (hj : IsTwoPow a (posWt a c j j)) : False := by
  fin_cases i <;> fin_cases j
  all_goals
    have hci := diag_mod_eq ha hi
    have hcj := diag_mod_eq ha hj
    simp only [Fin.reduceFinMk] at hci hcj
    first
      | exact (hij rfl).elim
      | omega

end CFSG.RepresentationTheory.SzMartineau
