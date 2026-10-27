module

public import CFSG.Quasithin.Vol2.Ch11SecBK10A
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryDiagonalOuterOrder

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecD

namespace BK10.U3

open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.ClassicalGroups.UnitaryFlag

variable {p : ℕ} {K : Type} [Field K]

theorem add_one_dvd_card {ℓ f : ℕ} (h : UnitaryFieldData ℓ f K) {n : ℕ} (hn : 3 ≤ n) :
    ℓ ^ f + 1 ∣ Nat.card (unitaryPSU h n) := by
  set q := ℓ ^ f with hq
  have hSint : (Nat.card (unitarySU ℓ f K n) : ℤ) = ((q : ℕ) : ℤ) ^ (n * (n - 1) / 2) *
      ∏ j ∈ Finset.Icc 2 n, (((q : ℕ) : ℤ) ^ j - (-1) ^ j) := by
    have hB := gramForm_isSymm h (G := (1 : Matrix (Fin n) (Fin n) K)) (by
      rw [Matrix.map_one _ (map_zero h.bar) (map_one h.bar), Matrix.transpose_one])
    have hBl := gramForm_separatingLeft h (G := (1 : Matrix (Fin n) (Fin n) K)) (by simp)
    have hdim : Module.finrank K (Fin n → K) = n := Module.finrank_fin_fun K
    rw [unitarySU_eq_gramSU h, card_gramSU]
    exact (CFSG.LinearGroups.unitary_full_group_order h hB hBl hdim (by omega)).2.1
  have hZ : Nat.card (unitaryScalars h n) = Nat.gcd n (q + 1) := card_unitaryScalars h (by omega)
  have hSZ : Nat.card (unitarySU ℓ f K n) = Nat.card (unitaryPSU h n) * Nat.gcd n (q + 1) := by
    rw [← hZ]
    exact Subgroup.card_eq_card_quotient_mul_card_subgroup _
  have hprod : (((q : ℕ) : ℤ) + 1) * (((q : ℕ) : ℤ) + 1) ∣
      ∏ j ∈ Finset.Icc 2 n, (((q : ℕ) : ℤ) ^ j - (-1) ^ j) := by
    have hsub : ({2, 3} : Finset ℕ) ⊆ Finset.Icc 2 n := by
      intro j hj
      simp only [Finset.mem_insert, Finset.mem_singleton] at hj
      rw [Finset.mem_Icc]
      omega
    refine dvd_trans ?_ (Finset.prod_dvd_prod_of_subset _ _ _ hsub)
    rw [Finset.prod_pair (by norm_num)]
    exact mul_dvd_mul (Dvd.intro (((q : ℕ) : ℤ) - 1) (by ring))
      (Dvd.intro (((q : ℕ) : ℤ) ^ 2 - ((q : ℕ) : ℤ) + 1) (by ring))
  have h1 : (((q : ℕ) : ℤ) + 1) * (((q : ℕ) : ℤ) + 1) ∣
      (Nat.card (unitaryPSU h n) : ℤ) * (((q : ℕ) : ℤ) + 1) := by
    refine (hprod.trans (Dvd.intro_left _ hSint.symm)).trans ?_
    rw [hSZ, Nat.cast_mul]
    exact mul_dvd_mul_left _ (by exact_mod_cast Nat.gcd_dvd_right n (q + 1))
  have h2 : ((q : ℕ) : ℤ) + 1 ∣ (Nat.card (unitaryPSU h n) : ℤ) :=
    (mul_dvd_mul_iff_right (by positivity)).1 h1
  exact_mod_cast h2

theorem eq_one_of_isCoprimePrimeAut_prime (h : UnitaryFieldData p 1 K) (hp2 : p ≠ 2)
    {β : MulAut (unitaryPSU h 3)} (hβ : IsCoprimePrimeAut β) : β = 1 := by
  have : Finite K := h.finite
  have hq : ¬(3 = 3 ∧ p ^ 1 = 2) := fun h32 => hp2 (by simpa using h32.2)
  obtain ⟨-, -, -, -, hout, -⟩ := unitary_full_diagonal_outer_order h (le_refl 3) hq
  have hdvd := add_one_dvd_card h (le_refl 3)
  refine eq_one_of_outer (fun q hq hqO => ?_) hβ
  rw [hout, pow_one, mul_one] at hqO
  have hp1 : 2 ∣ p + 1 := by
    obtain ⟨m, hm⟩ := h.prime.odd_of_ne_two hp2
    exact ⟨m + 1, by omega⟩
  rcases (Nat.Prime.dvd_mul hq).mp hqO with h2 | h3
  · have : q = 2 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp h2
    subst this
    rw [pow_one] at hdvd
    exact hp1.trans hdvd
  · rw [pow_one] at hdvd
    exact (h3.trans (Nat.gcd_dvd_right _ _)).trans hdvd

theorem torusRigid_prime (h : UnitaryFieldData p 1 K) (hp2 : p ≠ 2) :
    TorusRigid (unitaryPSU h 3) :=
  torusRigid_of_forall_eq_one fun _ hβ => eq_one_of_isCoprimePrimeAut_prime h hp2 hβ

end BK10.U3

end CFSG.Quasithin.Vol2.Ch11.SecD
