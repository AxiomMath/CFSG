module

public import CFSG.RankThree.Automorphisms.CoprimeCyclicTools
public import CFSG.LocalAnalysis.ComponentInitial.DiagonalSemilinear
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherAntiunitaryTransport
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherPrimeFormRealization

public section

namespace CFSG.RankThree.Automorphisms

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.ClassicalGroups.UnitaryFlag CFSG.LinearGroups
open CFSG.ComponentClassification.OuterAutomorphisms (inner)

theorem add_one_dvd_card_unitaryPSU {ℓ f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData ℓ f K)
    {n : ℕ} (hn : 3 ≤ n) : ℓ ^ f + 1 ∣ Nat.card (unitaryPSU h n) := by
  set q := ℓ ^ f with hq
  have hSint : (Nat.card (unitarySU ℓ f K n) : ℤ) = ((q : ℕ) : ℤ) ^ (n * (n - 1) / 2) *
      ∏ j ∈ Finset.Icc 2 n, (((q : ℕ) : ℤ) ^ j - (-1) ^ j) := by
    have hB := gramForm_isSymm h (G := (1 : Matrix (Fin n) (Fin n) K)) (by
      rw [Matrix.map_one _ (map_zero h.bar) (map_one h.bar), transpose_one])
    have hBl := gramForm_separatingLeft h (G := (1 : Matrix (Fin n) (Fin n) K)) (by simp)
    have hdim : Module.finrank K (Fin n → K) = n := Module.finrank_fin_fun K
    rw [unitarySU_eq_gramSU h, card_gramSU]
    exact (unitary_full_group_order h hB hBl hdim (by omega)).2.1
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

theorem unitary_coprime_odd_prime_automorphism_subgroups_cyclic {ℓ f : ℕ} {K : Type} [Field K]
    (h : UnitaryFieldData ℓ f K) {n : ℕ} (hn : 3 ≤ n) (hq : ¬(n = 3 ∧ ℓ ^ f = 2)) {p : ℕ}
    (hp : p.Prime) (_hodd : Odd p) (hpT : ¬ p ∣ Nat.card (unitaryPSU h n)) :
    (∀ P : Subgroup (MulAut (unitaryPSU h n)), IsPGroup p P → IsCyclic P) ∧
    ∀ (E : Type*) [Group E] [IsElementaryAbelian p E], Nat.card E = p ^ 2 →
      ∀ α : E →* MulAut (unitaryPSU h n), p ≤ Nat.card α.ker := by
  have : Fact p.Prime := ⟨hp⟩
  have : Finite K := h.finite
  have hC : IsPrimeFormGram (1 : GL (Fin n) K) := isPrimeFormGram_one
  obtain ⟨⟨eT⟩, -, -, -, -, -, -, hFker, -, hinn, hDI⟩ :=
    unitary_prime_form_full_semilinear_realization h hC hn hq
  set T' := primeFormP h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) with hT'
  set D := primeFormD h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) with hD
  set I := inner T' with hI
  have hpT' : ¬ p ∣ Nat.card T' := by
    rw [Nat.card_congr eT.toEquiv]
    exact hpT
  have hpq : Nat.Coprime (ℓ ^ f + 1) p :=
    ((Nat.Prime.coprime_iff_not_dvd hp).2 fun hd =>
      hpT (hd.trans (add_one_dvd_card_unitaryPSU h hn))).symm
  have hID : I ≤ D := fun α hα => by
    obtain ⟨s, rfl⟩ := (hinn α).1 hα
    exact ⟨_, rfl⟩
  have hDcop : Nat.Coprime (Nat.card D) p := by
    rw [← Subgroup.relIndex_mul_card I D, inf_of_le_left hID]
    exact Nat.Coprime.mul_left (Nat.Coprime.coprime_dvd_left hDI hpq)
      (coprime_card_inner hp hpT')
  have : IsCyclic (K ≃+* K) := (card_ringAut_and_isCyclic h.prime K h.card).2
  have hcyc' : ∀ P : Subgroup (MulAut T'), IsPGroup p P → IsCyclic P := fun P hP =>
    isCyclic_of_injective _ (injective_comp_of_isPGroup (primeFormFieldFactor h hC hn hq)
      (by rw [hFker]; exact hDcop) hP)
  have hcyc : ∀ P : Subgroup (MulAut (unitaryPSU h n)), IsPGroup p P → IsCyclic P :=
    fun P hP => isCyclic_of_isPGroup_of_mulEquiv eT.symm hcyc' hP
  exact ⟨hcyc, fun E _ _ hE α => le_card_ker_of_isElementaryAbelian hp hcyc hE α⟩

end CFSG.RankThree.Automorphisms
