module

public import CFSG.RankThree.Classical.SteinbergBTUnitarySubfield

public noncomputable section

namespace CFSG.RankThree.Classical

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag CFSG.LieType.Chevalley

theorem nonsplit_unitary_prime_subfield_fixed_group_and_full_centralizer {ℓ f n p : ℕ}
    {K : Type} [Field K] (h : UnitaryFieldData ℓ f K) (hn : 3 ≤ n) (hq : ¬(n = 3 ∧ ℓ ^ f = 2))
    (hp : p.Prime) (hp3 : 3 < p) (_hpℓ : p ≠ ℓ) (hpq : ¬p ∣ ℓ ^ f + 1) (σ : K ≃+* K)
    (hσ : orderOf σ = p) :
    p ∣ f ∧ Nat.card (fixSubfield σ) = (ℓ ^ (f / p)) ^ 2 ∧
      (∀ c : fixSubfield σ, h.bar c = (c : K) ^ ℓ ^ (f / p)) ∧
      Function.Injective (primeSubfieldPSU h hp (by omega) hσ n) ∧
      (primeSubfieldPSU h hp (by omega) hσ n).range = fieldFixedPSU h n σ ∧
      ((QuotientGroup.mk' (normOneScalars h
        (gramSU h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) n)).comp
          (primeSubfieldSU h hp (by omega) hσ n)).ker = primeSubfieldScalars h hp (by omega) hσ n ∧
      (normOneScalars h (gramSU h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) n).comap
          (primeSubfieldSU h hp (by omega) hσ n) = primeSubfieldScalars h hp (by omega) hσ n ∧
      Nat.card (normOneScalars h (gramSU h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) n) =
        Nat.gcd n (ℓ ^ f + 1) ∧
      Nat.card (primeSubfieldScalars h hp (by omega) hσ n) = Nat.gcd n (ℓ ^ (f / p) + 1) ∧
      (¬(n = 3 ∧ ℓ ^ (f / p) = 2) →
        IsSimpleGroup (fieldFixedPSU h n σ) ∧ (¬∀ x y : fieldFixedPSU h n σ, x * y = y * x) ∧
        fixingSubgroup (MulAut (primeFormP h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)))
            (fieldFixedPSU h n σ : Set (primeFormP h
              ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K))) =
          (fixingSubgroup (K ≃+* K) (fixSubfield σ : Set K)).map
            (primeFormFieldHom h (isPrimeFormGram_one (n := n))) ∧
        (fixingSubgroup (K ≃+* K) (fixSubfield σ : Set K)).map
            (primeFormFieldHom h (isPrimeFormGram_one (n := n))) =
          Subgroup.zpowers (primeFormFieldHom h (isPrimeFormGram_one (n := n)) σ) ∧
        Nat.card (Subgroup.zpowers (primeFormFieldHom h (isPrimeFormGram_one (n := n)) σ)) = p) ∧
      (n = 3 ∧ ℓ ^ (f / p) = 2 →
        Nat.card (fieldFixedPSU h n σ) = 72 ∧ ∀ x ∈ fieldFixedPSU h n σ, orderOf x ≠ p) := by
  have hp2 : p ≠ 2 := by omega
  have hZ : ¬p ∣ Nat.card (normOneScalars h
      (gramSU h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) n) := by
    rw [card_normOneScalars_one h (by omega)]
    exact fun hd => hpq (hd.trans (Nat.gcd_dvd_right _ _))
  obtain ⟨hpf, hcard, hbar, hker, hcomap, hinj, hrange, hZ1, hZ0, hsimple, h72⟩ :=
    prime_subfield_fixed_group_package h hp hp2 hσ n hn hq hZ
  exact ⟨hpf, hcard, hbar, hinj, hrange, hker, hcomap, hZ1, hZ0, hsimple,
    fun hq₀ => h72 hq₀ hp3⟩

end CFSG.RankThree.Classical
