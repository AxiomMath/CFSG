module

public import Mathlib.Data.Matrix.Mul
public import Mathlib.SetTheory.Cardinal.Finite
public import Mathlib.Data.Nat.Prime.Defs
import CFSG.GroupTheory.WeirSylow.OrthogonalOrders
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.GroupWithZero.Invertible

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open Matrix

private theorem uc22s2112r34q35_prime_not_dvd_two_three_five {s : ℕ}
    (hs : s.Prime) (hs7 : 7 ≤ s) {a b c : ℕ} : ¬ s ∣ 2 ^ a * 3 ^ b * 5 ^ c := by
  intro hd
  rcases (Nat.Prime.dvd_mul hs).mp hd with h | h5
  · rcases (Nat.Prime.dvd_mul hs).mp h with h2 | h3
    · have hd2 : s ∣ 2 := hs.dvd_of_dvd_pow h2
      have : s = 2 := (Nat.prime_dvd_prime_iff_eq hs Nat.prime_two).mp hd2
      omega
    · have hd3 : s ∣ 3 := hs.dvd_of_dvd_pow h3
      have : s = 3 := (Nat.prime_dvd_prime_iff_eq hs Nat.prime_three).mp hd3
      omega
  · have hd5 : s ∣ 5 := hs.dvd_of_dvd_pow h5
    have : s = 5 :=
      (Nat.prime_dvd_prime_iff_eq hs (by norm_num : Nat.Prime 5)).mp hd5
    omega

private theorem uc22s2112r34q35_nondegenerate {n : ℕ} {K : Type} [Field K]
    (h2 : (2 : K) ≠ 0) {c : Fin n → K} (hc : ∀ i, c i ≠ 0) :
    (QuadraticMap.polarBilin (QuadraticMap.weightedSumSquares K c)).Nondegenerate := by
  let : Invertible (2 : K) := invertibleOfNonzero h2
  exact QuadraticMap.nondegenerate_polar_iff.mpr
    (QuadraticMap.nondegenerate_weightedSumSquares (w := c)
      (fun i => isRegular_iff_ne_zero.mpr (hc i)))

private theorem uc22s2112r34q35_orderOf_dvd {n : ℕ} {K : Type} [Field K]
    (_h2 : (2 : K) ≠ 0) {c : Fin n → K} (_hc : ∀ i, c i ≠ 0) {g : GL (Fin n) K}
    (hg : ∀ v : Fin n → K,
      ∑ i, c i * (((g : Matrix (Fin n) (Fin n) K) *ᵥ v) i) ^ 2 = ∑ i, c i * v i ^ 2) :
    orderOf g ∣ Nat.card (TauCeti.QuadraticMap.orthogonalGroup
      (QuadraticMap.weightedSumSquares K c)) := by
  let Q : QuadraticForm K (Fin n → K) := QuadraticMap.weightedSumSquares K c
  have hQ : ⇑Q = fun v : Fin n → K => ∑ i, c i * v i ^ 2 := by
    funext v
    change QuadraticMap.weightedSumSquares K c v = ∑ i, c i * v i ^ 2
    rw [QuadraticMap.weightedSumSquares_apply]
    simp [smul_eq_mul, pow_two]
  have hmem : CFSG.ClassicalGroups.Orthogonal.toLinEquiv (Fin n) K g ∈
      TauCeti.QuadraticMap.orthogonalGroup Q := by
    rw [TauCeti.QuadraticMap.mem_orthogonalGroup_iff]
    intro v
    rw [CFSG.ClassicalGroups.Orthogonal.toLinEquiv_apply, hQ]
    exact hg v
  have h := Subgroup.orderOf_dvd_natCard (TauCeti.QuadraticMap.orthogonalGroup Q) hmem
  rw [MulEquiv.orderOf_eq (CFSG.ClassicalGroups.Orthogonal.toLinEquiv (Fin n) K) g] at h
  exact h

theorem uc22s2112r34q35_eq_one_of_isometry_four {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 3 ∨ Nat.card K = 5) {c : Fin 4 → K} (hc : ∀ i, c i ≠ 0)
    {A : Matrix (Fin 4) (Fin 4) K}
    (hA : ∀ v : Fin 4 → K, ∑ i, c i * (A *ᵥ v) i ^ 2 = ∑ i, c i * v i ^ 2) {s : ℕ}
    (hs : s.Prime) (hs7 : 7 ≤ s) (hs13 : s ≠ 13) (hAs : A ^ s = 1) : A = 1 := by
  classical
  let : Fintype K := Fintype.ofFinite K
  have hodd : Odd (Nat.card K) := by
    rcases hK with h | h
    · rw [h]; exact ⟨1, by norm_num⟩
    · rw [h]; exact ⟨2, by norm_num⟩
  have hchar : ringChar K ≠ 2 := by
    intro h
    have hcard : Fintype.card K % 2 = 0 := FiniteField.even_card_of_char_two h
    have hodd' : Odd (Fintype.card K) := by simpa [Nat.card_eq_fintype_card] using hodd
    exact hodd'.not_two_dvd_nat (Nat.dvd_of_mod_eq_zero hcard)
  have h2 : (2 : K) ≠ 0 := by
    intro hzero
    exact hchar (by
      have : CharP K 2 := CFSG.GroupTheory.WeirSylow.charP_two_of_two_eq_zero hzero
      exact ringChar.eq K 2)
  have hs1 : 1 ≤ s := hs.one_lt.le
  have hmul : A * A ^ (s - 1) = 1 := by
    calc A * A ^ (s - 1) = A ^ 1 * A ^ (s - 1) := by rw [pow_one]
      _ = A ^ (1 + (s - 1)) := by rw [pow_add]
      _ = A ^ s := by rw [show 1 + (s - 1) = s by omega]
      _ = 1 := hAs
  have hmul' : A ^ (s - 1) * A = 1 := by
    calc A ^ (s - 1) * A = A ^ (s - 1) * A ^ 1 := by rw [pow_one]
      _ = A ^ ((s - 1) + 1) := by rw [pow_add]
      _ = A ^ s := by rw [Nat.sub_add_cancel hs1]
      _ = 1 := hAs
  let g : GL (Fin 4) K := Units.mk A (A ^ (s - 1)) hmul hmul'
  have hgcoe : ((g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) = A := rfl
  have hgs : g ^ s = 1 := by
    apply Units.ext
    simp only [Units.val_pow_eq_pow_val, hgcoe, hAs, Units.val_one]
  have hgdvd : orderOf g ∣ s := orderOf_dvd_of_pow_eq_one hgs
  have hdiv : orderOf g ∣ Nat.card (TauCeti.QuadraticMap.orthogonalGroup
      (QuadraticMap.weightedSumSquares K c)) :=
    uc22s2112r34q35_orderOf_dvd h2 hc (g := g) (by simpa [hgcoe] using hA)
  have hB := uc22s2112r34q35_nondegenerate (n := 4) h2 hc
  have hdim : Module.finrank K (Fin 4 → K) = 2 * (1 + 1) := by
    rw [Module.finrank_fin_fun]
  have hprod : (∏ i ∈ Finset.Icc 1 1, (((Nat.card K : ℤ) ^ 2) ^ i - 1)) =
      ((Nat.card K : ℤ) ^ 2 - 1) := by simp
  have hnot : ¬ s ∣ Nat.card (TauCeti.QuadraticMap.orthogonalGroup
      (QuadraticMap.weightedSumSquares K c)) := by
    intro hdvd
    by_cases hp : CFSG.GroupTheory.WeirSylow.IsPlusType
        (QuadraticMap.weightedSumSquares K c)
    · have hraw := CFSG.GroupTheory.WeirSylow.natCard_orthogonalGroup_of_type
          (K := K) (V := Fin 4 → K) hB (m := 1) hdim (ε := 1) (Or.inl ⟨rfl, hp⟩)
      rw [hprod] at hraw
      rcases hK with hq | hq
      · have hval : (Nat.card (TauCeti.QuadraticMap.orthogonalGroup
            (QuadraticMap.weightedSumSquares K c)) : ℤ) = 1152 := by
          rw [hraw, hq]
          norm_num
        have hcard : Nat.card (TauCeti.QuadraticMap.orthogonalGroup
            (QuadraticMap.weightedSumSquares K c)) = 1152 := by
          exact_mod_cast hval
        rw [hcard, show (1152 : ℕ) = 2 ^ 7 * 3 ^ 2 * 5 ^ 0 by norm_num] at hdvd
        exact uc22s2112r34q35_prime_not_dvd_two_three_five hs hs7 hdvd
      · have hval : (Nat.card (TauCeti.QuadraticMap.orthogonalGroup
            (QuadraticMap.weightedSumSquares K c)) : ℤ) = 28800 := by
          rw [hraw, hq]
          norm_num
        have hcard : Nat.card (TauCeti.QuadraticMap.orthogonalGroup
            (QuadraticMap.weightedSumSquares K c)) = 28800 := by
          exact_mod_cast hval
        rw [hcard, show (28800 : ℕ) = 2 ^ 7 * 3 ^ 2 * 5 ^ 2 by norm_num] at hdvd
        exact uc22s2112r34q35_prime_not_dvd_two_three_five hs hs7 hdvd
    · have hraw := CFSG.GroupTheory.WeirSylow.natCard_orthogonalGroup_of_type
          (K := K) (V := Fin 4 → K) hB (m := 1) hdim (ε := -1) (Or.inr ⟨rfl, hp⟩)
      rw [hprod] at hraw
      rcases hK with hq | hq
      · have hval : (Nat.card (TauCeti.QuadraticMap.orthogonalGroup
            (QuadraticMap.weightedSumSquares K c)) : ℤ) = 1440 := by
          rw [hraw, hq]
          norm_num
        have hcard : Nat.card (TauCeti.QuadraticMap.orthogonalGroup
            (QuadraticMap.weightedSumSquares K c)) = 1440 := by
          exact_mod_cast hval
        rw [hcard, show (1440 : ℕ) = 2 ^ 5 * 3 ^ 2 * 5 ^ 1 by norm_num] at hdvd
        exact uc22s2112r34q35_prime_not_dvd_two_three_five hs hs7 hdvd
      · have hval : (Nat.card (TauCeti.QuadraticMap.orthogonalGroup
            (QuadraticMap.weightedSumSquares K c)) : ℤ) = 31200 := by
          rw [hraw, hq]
          norm_num
        have hcard : Nat.card (TauCeti.QuadraticMap.orthogonalGroup
            (QuadraticMap.weightedSumSquares K c)) = 31200 := by
          exact_mod_cast hval
        rw [hcard, show (31200 : ℕ) = 2 ^ 5 * 3 ^ 1 * 5 ^ 2 * 13 by norm_num] at hdvd
        rcases (Nat.Prime.dvd_mul hs).mp hdvd with h | h13
        · exact uc22s2112r34q35_prime_not_dvd_two_three_five hs hs7 h
        · exact hs13 ((Nat.prime_dvd_prime_iff_eq hs (by norm_num : Nat.Prime 13)).mp h13)
  have horder_eq : orderOf g = 1 := by
    rcases Nat.Prime.eq_one_or_self_of_dvd hs (orderOf g) hgdvd with h | h
    · exact h
    · exact absurd (h ▸ hdiv) hnot
  have hgone : g = 1 := orderOf_eq_one_iff.mp horder_eq
  calc A = ((g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) := hgcoe.symm
    _ = ((1 : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) := by rw [hgone]
    _ = 1 := rfl

theorem uc22s2112r34q35_eq_one_of_isometry_three {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 3 ∨ Nat.card K = 5) {c : Fin 3 → K} (hc : ∀ i, c i ≠ 0)
    {A : Matrix (Fin 3) (Fin 3) K}
    (hA : ∀ v : Fin 3 → K, ∑ i, c i * (A *ᵥ v) i ^ 2 = ∑ i, c i * v i ^ 2) {s : ℕ}
    (hs : s.Prime) (hs7 : 7 ≤ s) (hAs : A ^ s = 1) : A = 1 := by
  classical
  let : Fintype K := Fintype.ofFinite K
  have hodd : Odd (Nat.card K) := by
    rcases hK with h | h
    · rw [h]; exact ⟨1, by norm_num⟩
    · rw [h]; exact ⟨2, by norm_num⟩
  have hchar : ringChar K ≠ 2 := by
    intro h
    have hcard : Fintype.card K % 2 = 0 := FiniteField.even_card_of_char_two h
    have hodd' : Odd (Fintype.card K) := by simpa [Nat.card_eq_fintype_card] using hodd
    exact hodd'.not_two_dvd_nat (Nat.dvd_of_mod_eq_zero hcard)
  have h2 : (2 : K) ≠ 0 := by
    intro hzero
    exact hchar (by
      have : CharP K 2 := CFSG.GroupTheory.WeirSylow.charP_two_of_two_eq_zero hzero
      exact ringChar.eq K 2)
  have hs1 : 1 ≤ s := hs.one_lt.le
  have hmul : A * A ^ (s - 1) = 1 := by
    calc A * A ^ (s - 1) = A ^ 1 * A ^ (s - 1) := by rw [pow_one]
      _ = A ^ (1 + (s - 1)) := by rw [pow_add]
      _ = A ^ s := by rw [show 1 + (s - 1) = s by omega]
      _ = 1 := hAs
  have hmul' : A ^ (s - 1) * A = 1 := by
    calc A ^ (s - 1) * A = A ^ (s - 1) * A ^ 1 := by rw [pow_one]
      _ = A ^ ((s - 1) + 1) := by rw [pow_add]
      _ = A ^ s := by rw [Nat.sub_add_cancel hs1]
      _ = 1 := hAs
  let g : GL (Fin 3) K := Units.mk A (A ^ (s - 1)) hmul hmul'
  have hgcoe : ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = A := rfl
  have hgs : g ^ s = 1 := by
    apply Units.ext
    simp only [Units.val_pow_eq_pow_val, hgcoe, hAs, Units.val_one]
  have hgdvd : orderOf g ∣ s := orderOf_dvd_of_pow_eq_one hgs
  have hdiv : orderOf g ∣ Nat.card (TauCeti.QuadraticMap.orthogonalGroup
      (QuadraticMap.weightedSumSquares K c)) :=
    uc22s2112r34q35_orderOf_dvd h2 hc (g := g) (by simpa [hgcoe] using hA)
  have hB := uc22s2112r34q35_nondegenerate (n := 3) h2 hc
  have hdim : Module.finrank K (Fin 3 → K) = 2 * 1 + 1 := by
    rw [Module.finrank_fin_fun]
  have hprod : (∏ i ∈ Finset.Icc 1 1, (((Nat.card K : ℤ) ^ 2) ^ i - 1)) =
      ((Nat.card K : ℤ) ^ 2 - 1) := by simp
  have hnot : ¬ s ∣ Nat.card (TauCeti.QuadraticMap.orthogonalGroup
      (QuadraticMap.weightedSumSquares K c)) := by
    intro hdvd
    have hraw := CFSG.GroupTheory.WeirSylow.natCard_orthogonalGroup_odd
        (K := K) (V := Fin 3 → K) hchar hB (n := 1) hdim
    rw [hprod] at hraw
    rcases hK with hq | hq
    · have hval : (Nat.card (TauCeti.QuadraticMap.orthogonalGroup
          (QuadraticMap.weightedSumSquares K c)) : ℤ) = 48 := by
        rw [hraw, hq]
        norm_num
      have hcard : Nat.card (TauCeti.QuadraticMap.orthogonalGroup
          (QuadraticMap.weightedSumSquares K c)) = 48 := by
        exact_mod_cast hval
      rw [hcard, show (48 : ℕ) = 2 ^ 4 * 3 ^ 1 * 5 ^ 0 by norm_num] at hdvd
      exact uc22s2112r34q35_prime_not_dvd_two_three_five hs hs7 hdvd
    · have hval : (Nat.card (TauCeti.QuadraticMap.orthogonalGroup
          (QuadraticMap.weightedSumSquares K c)) : ℤ) = 240 := by
        rw [hraw, hq]
        norm_num
      have hcard : Nat.card (TauCeti.QuadraticMap.orthogonalGroup
          (QuadraticMap.weightedSumSquares K c)) = 240 := by
        exact_mod_cast hval
      rw [hcard, show (240 : ℕ) = 2 ^ 4 * 3 ^ 1 * 5 ^ 1 by norm_num] at hdvd
      exact uc22s2112r34q35_prime_not_dvd_two_three_five hs hs7 hdvd
  have horder_eq : orderOf g = 1 := by
    rcases Nat.Prime.eq_one_or_self_of_dvd hs (orderOf g) hgdvd with h | h
    · exact h
    · exact absurd (h ▸ hdiv) hnot
  have hgone : g = 1 := orderOf_eq_one_iff.mp horder_eq
  calc A = ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) := hgcoe.symm
    _ = ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) := by rw [hgone]
    _ = 1 := rfl

end CFSG.LocalAnalysis.UniquenessCase.UC22
