module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.K2LieDefs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82

open CFSG.Open Subgroup
open CFSG.Blueprint (LieModel)
open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.ClassicalGroups.UnitaryFlag (gramSU unitaryPSUEquiv)
open CFSG.ComponentClassification.OuterAutomorphisms (inner)

private theorem exists3_psu_primeFormD_mem_inner {p f n : ℕ} {K : Type} [Field K]
    (h : UnitaryFieldData p f K) (hn : 3 ≤ n) (hq : ¬(n = 3 ∧ p ^ f = 2))
    (h3 : ¬ 3 ∣ Nat.gcd n (p ^ f + 1))
    {δ : MulAut (primeFormP h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K))}
    (hδ : δ ∈ primeFormD h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K))
    {k : ℕ} (hk : δ ^ 3 ^ k = 1) :
    δ ∈ inner (primeFormP h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) := by
  obtain ⟨-, -, hcard, -⟩ := unitary_full_diagonal_outer_order h hn hq
  set T := primeFormP h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)
  set D := primeFormD h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)
  set I := inner T
  set x : D ⧸ I.subgroupOf D := QuotientGroup.mk (⟨δ, hδ⟩ : D) with hx
  have hxk : x ^ 3 ^ k = 1 := by
    rw [hx, ← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
    change (δ ^ 3 ^ k : MulAut (primeFormP h ((1 : GL (Fin n) K) :
      Matrix (Fin n) (Fin n) K))) ∈ I
    rw [hk]
    exact one_mem I
  have hdvd1 : orderOf x ∣ 3 ^ k := orderOf_dvd_of_pow_eq_one hxk
  have hdvd2 : orderOf x ∣ Nat.gcd n (p ^ f + 1) := hcard ▸ orderOf_dvd_natCard x
  have hcop : Nat.Coprime (3 ^ k) (Nat.gcd n (p ^ f + 1)) :=
    Nat.Coprime.pow_left k ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr h3)
  have hx1 : orderOf x = 1 := Nat.eq_one_of_dvd_coprimes hcop hdvd1 hdvd2
  have hmem := (QuotientGroup.eq_one_iff (⟨δ, hδ⟩ : D)).mp (orderOf_eq_one_iff.mp hx1)
  exact Subgroup.mem_subgroupOf.mp hmem

private theorem exists3_psu_primeFormP {p f n : ℕ} {K : Type} [Field K]
    (h : UnitaryFieldData p f K) (hn : 3 ≤ n) (hq : ¬(n = 3 ∧ p ^ f = 2))
    (h3 : ¬ 3 ∣ Nat.gcd n (p ^ f + 1)) :
    Exists3 (primeFormP h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) := by
  intro hφ
  obtain ⟨φ, hφn, k, hφk⟩ := hφ
  have hC : IsPrimeFormGram (1 : GL (Fin n) K) := isPrimeFormGram_one
  obtain ⟨-, -, -, -, -, -, -, hker, -, hinn, -⟩ :=
    unitary_prime_form_full_semilinear_realization h hC hn hq
  set T := primeFormP h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)
  set D := primeFormD h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)
  set ρ := primeFormFieldFactor h hC hn hq
  set τ := ρ φ with hτ
  have hID : inner T ≤ D := fun α hα => by
    obtain ⟨s, rfl⟩ := (hinn α).1 hα
    exact ⟨⟨s, s.2.1⟩, rfl⟩
  have hτk : τ ^ 3 ^ k = 1 := by
    rw [hτ, ← map_pow, hφk, map_one]
  have hτne : τ ≠ 1 := by
    intro hτ1
    have hφD : φ ∈ D := by
      rw [← hker, MonoidHom.mem_ker, ← hτ]
      exact hτ1
    exact hφn (exists3_psu_primeFormD_mem_inner h hn hq h3 hφD hφk)
  obtain ⟨σ, hσ3, hσne⟩ := exists_pow_three_eq_one_of_pow_three_pow_eq_one hτne hτk
  have hfac : primeFormFieldFactor h hC hn hq (primeFormFieldHom h hC σ) = σ := by
    have := primeFormFieldFactor_apply h hC hn hq
      (1 : primeFormUnitary h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) σ
    rwa [map_one, one_mul] at this
  refine ⟨primeFormFieldHom h hC σ, ?_, ?_⟩
  · rw [← map_pow, hσ3, map_one]
  · intro hmem
    have h1 : primeFormFieldFactor h hC hn hq (primeFormFieldHom h hC σ) = 1 := by
      rw [← MonoidHom.mem_ker, hker]
      exact hID hmem
    exact hσne (hfac ▸ h1)

theorem exists3_psu {X : Type} [Group X] [Finite X] {n r f : ℕ} (hn : 4 ≤ n) (hr : r.Prime)
    (h : LieModel X .PSU n r f) (h3 : ¬ 3 ∣ Nat.gcd n (r ^ f + 1)) : Exists3 X := by
  have hn0 : n ≠ 0 := by omega
  have hscm : StatedClassicalModel X .PSU n r f :=
    CFSG.Blueprint.LieModel.statedClassicalModel_of_ne_zero hn0 h
  obtain ⟨⟨hℓ, hm, hn3, hne⟩, K, _, _, hK, ⟨e⟩⟩ := hscm
  have hU : UnitaryFieldData r f K := ⟨hℓ, hm, by rw [hK, ← pow_mul, mul_comm]⟩
  have hq : ¬(n = 3 ∧ r ^ f = 2) := fun ⟨h1, h2⟩ => hne (by rw [h1, h2])
  obtain ⟨⟨eT⟩, -⟩ := unitary_prime_form_full_semilinear_realization hU
    (isPrimeFormGram_one (n := n)) hn3 hq
  have e' : X ≃* primeFormP hU ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) :=
    (e.trans (unitaryPSUEquiv hU (by omega)).symm).trans eT.symm
  exact exists3_of_mulEquiv e' (exists3_psu_primeFormP hU hn3 hq h3)

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82
