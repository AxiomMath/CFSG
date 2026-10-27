module

public import CFSG.RankThree.PartOne.KC.UnitaryCrossPrimeModel
public import CFSG.RankThree.PartOne.KC.LinearPlaneStatements

public section

namespace CFSG.RankThree.PartOne

open Subgroup CFSG CFSG.RankThree.LocalRank CFSG.Assembly CFSG.Assembly.LowTwoRank
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag CFSG.RankThree.PartOne.KCUnitaryModel
open CFSG.Assembly.RankThreeEven (localRank)
open scoped Pointwise

abbrev innU {ℓ f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData ℓ f K) (n : ℕ) :
    Subgroup (MulAut (primeFormP h (idGram K n))) :=
  (MulAut.conj : primeFormP h (idGram K n) →* MulAut (primeFormP h (idGram K n))).range

theorem exists_primeFormP_of_statedClassicalModel_PSU {T : Type} [Group T] {n ℓ f : ℕ}
    (hmod : StatedClassicalModel T .PSU n ℓ f) :
    ℓ.Prime ∧ 1 ≤ f ∧ 3 ≤ n ∧ ¬(n = 3 ∧ ℓ ^ f = 2) ∧
      ∃ (K : Type) (_ : Field K) (h : UnitaryFieldData ℓ f K),
        Nonempty (T ≃* primeFormP h (idGram K n)) := by
  obtain ⟨⟨hℓ, hf, hn, hne⟩, K, _, _, hK, ⟨e⟩⟩ := hmod
  have hne' : ¬(n = 3 ∧ ℓ ^ f = 2) := fun ⟨h1, h2⟩ => hne (by rw [h1, h2])
  have hU : UnitaryFieldData ℓ f K := ⟨hℓ, hf, by rw [hK, ← pow_mul, mul_comm]⟩
  refine ⟨hℓ, hf, hn, hne', K, inferInstance, hU, ⟨?_⟩⟩
  exact (e.trans (unitaryPSUEquiv hU (by omega)).symm).trans
    (Classical.choice (unitary_prime_form_full_semilinear_realization hU
      (isPrimeFormGram_idGram (K := K) (n := n)) hn hne').1).symm

@[expose] def UnitaryNonsplitInnerPlaneProductsTrivial : Prop :=
  ∀ (ℓ f n p : ℕ) (K : Type) [Field K] (h : UnitaryFieldData ℓ f K), p.Prime → 3 < p →
    p ≠ ℓ → ¬ p ∣ ℓ ^ f + 1 → 3 ≤ n → ¬(n = 3 ∧ ℓ ^ f = 2) →
    ∀ B : Subgroup (MulAut (primeFormP h (idGram K n))), innU h n ≤ B →
    ∀ A : Subgroup (MulAut (primeFormP h (idGram K n))), A ≤ innU h n → IsElementaryAbelian p A →
      Nat.card A = p ^ 2 →
      autThetaT p B A = ⊥ ∧ ∀ t ∈ A, t ≠ 1 → autPlaneProduct p B A t = ⊥

@[expose] def NonsplitUnitaryNoninnerPlaneLocalCoreOdd : Prop :=
  ∀ (ℓ f n p : ℕ) (K : Type) [Field K] (h : UnitaryFieldData ℓ f K), p.Prime → 3 < p →
    p ≠ ℓ → ¬ p ∣ ℓ ^ f + 1 → 3 ≤ n → ¬(n = 3 ∧ ℓ ^ f = 2) →
    ∀ B : Subgroup (MulAut (primeFormP h (idGram K n))), innU h n ≤ B →
    ∀ A : Subgroup (MulAut (primeFormP h (idGram K n))), A ≤ B → IsElementaryAbelian p A →
      Nat.card A = p ^ 2 → ¬ A ≤ innU h n →
      Nat.card (A ⊓ innU h n : Subgroup (MulAut (primeFormP h (idGram K n)))) = p ∧ p ∣ f ∧
      2 ^ p ≤ ℓ ^ f ∧ 3 < ℓ ^ f ∧
      (∀ a ∈ A, a ∉ innU h n →
        inSubgroup (aschbacherSolvableCore p) (B ⊓ Subgroup.centralizer {a}) = ⊥) ∧
      autThetaT p B A = ⊥ ∧
      ∀ t ∈ A, t ≠ 1 →
        PlaneProductIsSubgroup p B A t ∧
        ¬ 2 ∣ Nat.card (autPlaneProduct p B A t) ∧ (t ∉ innU h n → autPlaneProduct p B A t = ⊥)

@[expose] def HigherUnitaryInnerPlaneProductsTrivial : Prop :=
  ∀ (ℓ f n p : ℕ) (K : Type) [Field K] (h : UnitaryFieldData ℓ f K), p.Prime → p ≠ ℓ →
    3 ≤ n → n < p → ¬(n = 3 ∧ ℓ ^ f = 2) →
    ∀ B : Subgroup (MulAut (primeFormP h (idGram K n))), innU h n ≤ B →
    ∀ A : Subgroup (MulAut (primeFormP h (idGram K n))), A ≤ innU h n → IsElementaryAbelian p A →
      Nat.card A = p ^ 2 →
      autThetaT p B A = ⊥ ∧ ∀ t ∈ A, t ≠ 1 → autPlaneProduct p B A t = ⊥

@[expose] def HigherUnitaryNoninnerPlaneLocalCoreOdd : Prop :=
  ∀ (ℓ f n p : ℕ) (K : Type) [Field K] (h : UnitaryFieldData ℓ f K), p.Prime → p ≠ ℓ →
    3 ≤ n → n < p → ¬(n = 3 ∧ ℓ ^ f = 2) →
    ∀ B : Subgroup (MulAut (primeFormP h (idGram K n))), innU h n ≤ B →
    ∀ A : Subgroup (MulAut (primeFormP h (idGram K n))), A ≤ B → IsElementaryAbelian p A →
      Nat.card A = p ^ 2 → ¬ A ≤ innU h n →
      p ∣ f ∧ 2 ^ p ≤ ℓ ^ f ∧ 3 < ℓ ^ f ∧
      Nat.card (A ⊓ innU h n : Subgroup (MulAut (primeFormP h (idGram K n)))) = p ∧
      (∀ a ∈ A, a ∉ innU h n →
        inSubgroup (aschbacherSolvableCore p) (B ⊓ Subgroup.centralizer {a}) = ⊥) ∧
      autThetaT p B A = ⊥ ∧
      ∀ t ∈ A, t ≠ 1 →
        PlaneProductIsSubgroup p B A t ∧ ¬ 2 ∣ Nat.card (autPlaneProduct p B A t)

end CFSG.RankThree.PartOne
