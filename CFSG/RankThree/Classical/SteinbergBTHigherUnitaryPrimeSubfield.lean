module

public import CFSG.RankThree.Classical.SteinbergBTUnitarySubfield

public noncomputable section

namespace CFSG.RankThree.Classical

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag CFSG.LieType.Chevalley

theorem higher_unitary_prime_subfield_fixed_group_and_full_centralizer {ℓ f n p : ℕ} {K : Type}
    [Field K] (h : UnitaryFieldData ℓ f K) (hn : 3 ≤ n) (hnp : n < p) (hp : p.Prime)
    (hq : ¬(n = 3 ∧ ℓ ^ f = 2)) (σ : K ≃+* K) (hσ : orderOf σ = p) :
    p ∣ f ∧ Nat.card (fixSubfield σ) = (ℓ ^ (f / p)) ^ 2 ∧
      (∀ c : fixSubfield σ, h.bar c = (c : K) ^ ℓ ^ (f / p)) ∧
      Function.Injective (primeSubfieldPSU h hp (by omega) hσ n) ∧
      (primeSubfieldPSU h hp (by omega) hσ n).range = fieldFixedPSU h n σ ∧
      (primeSubfieldScalars h hp (by omega) hσ n).map (primeSubfieldSU h hp (by omega) hσ n) =
        normOneScalars h (gramSU h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) n ∧
      Nat.card (normOneScalars h (gramSU h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) n) =
        Nat.gcd n (ℓ ^ f + 1) ∧
      Nat.card (primeSubfieldScalars h hp (by omega) hσ n) = Nat.gcd n (ℓ ^ (f / p) + 1) ∧
      Nat.gcd n (ℓ ^ f + 1) = Nat.gcd n (ℓ ^ (f / p) + 1) ∧
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
  have := h.finite
  have hp2 : p ≠ 2 := by omega
  have hZcard := card_normOneScalars_one h (n := n) (by omega)
  have hZ : ¬p ∣ Nat.card (normOneScalars h
      (gramSU h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) n) := by
    rw [hZcard]
    exact Nat.not_dvd_of_pos_of_lt (Nat.gcd_pos_of_pos_left _ (by omega))
      ((Nat.gcd_le_left _ (by omega)).trans_lt hnp)
  obtain ⟨hpf, hcard, hbar, -, -, hinj, hrange, hZ1, hZ0, hsimple, h72⟩ :=
    prime_subfield_fixed_group_package h hp hp2 hσ n hn hq hZ
  have hmap := map_subfieldSU_normOneScalars h n (fixSubfield_unitaryFieldData h hp hp2 hσ)
    (fixSubfield_unitaryFieldData_bar h hp hp2 hσ)
    fun c hc => apply_eq_self_of_pow_eq_one n hp hσ (by omega) hnp hc
  have hgcd : Nat.gcd n (ℓ ^ f + 1) = Nat.gcd n (ℓ ^ (f / p) + 1) := by
    rw [← hZ1, ← hZ0, ← hmap, Subgroup.card_map_of_injective
      (subfieldSU_injective h (fixSubfield_unitaryFieldData h hp hp2 hσ)
        (fixSubfield_unitaryFieldData_bar h hp hp2 hσ) n)]
  exact ⟨hpf, hcard, hbar, hinj, hrange, hmap, hZ1, hZ0, hgcd, hsimple,
    fun hq₀ => h72 hq₀ (by omega)⟩

end CFSG.RankThree.Classical
