module

public import CFSG.Quasithin.SteinbergOuterPrimeControl

public noncomputable section

namespace CFSG.Quasithin.OuterPrimeControl

open Matrix CFSG.ClassicalGroups.UnitaryFlag
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.LocalAnalysis.ComponentInitial.OuterDerived
open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner equivalence)

variable {p f : ℕ} {K : Type} [Field K] {n : ℕ}

theorem exists_unitary_outer_field_factor (h : UnitaryFieldData p f K) (hn : 3 ≤ n)
    (hq : ¬(n = 3 ∧ p ^ f = 2)) :
    ∃ F : Outer (primeFormP h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) →* (K ≃+* K),
      Nat.card F.ker ∣ Nat.gcd n (p ^ f + 1) := by
  have hC : IsPrimeFormGram (1 : GL (Fin n) K) := isPrimeFormGram_one
  obtain ⟨-, -, -, -, -, -, -, hFker, -, hinn, -⟩ :=
    unitary_prime_form_full_semilinear_realization h hC hn hq
  obtain ⟨-, hcyc, hcard, -⟩ := unitary_full_diagonal_outer_order h hn hq
  have hID : inner (primeFormP h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) ≤
      (primeFormFieldFactor h hC hn hq).ker := by
    rw [hFker]
    intro α hα
    obtain ⟨s, rfl⟩ := (hinn α).1 hα
    exact ⟨_, rfl⟩
  refine ⟨QuotientGroup.lift _ (primeFormFieldFactor h hC hn hq) hID, ?_⟩
  rw [QuotientGroup.ker_lift, hFker]
  exact (isCyclic_map_mk_and_card_dvd _ _ hcyc).2.trans (dvd_of_eq hcard)

theorem perfect_unitary_central_quotient_outer_prime_control (h : UnitaryFieldData p f K)
    (hn : 3 ≤ n) (hq : ¬(n = 3 ∧ p ^ f = 2)) (J : Type*) [Group J] [Finite J]
    [Group.IsPerfect J] (e : J ⧸ Subgroup.center J ≃* unitaryPSU h n) :
    Nat.card (Outer J) ∣ 2 * f * Nat.gcd n (p ^ f + 1) ∧
    (∀ ℓ : ℕ, ℓ.Prime → ¬ ℓ ∣ Nat.gcd n (p ^ f + 1) →
      (∀ P : Sylow ℓ (Outer J), IsCyclic P) ∧ CFSG.pRank ℓ (Outer J) ≤ 1) ∧
    (n = 3 → ∀ ℓ : ℕ, ℓ.Prime → 5 ≤ ℓ →
      (∀ P : Sylow ℓ (Outer J), IsCyclic P) ∧ CFSG.pRank ℓ (Outer J) ≤ 1) ∧
    (Nat.gcd n (p ^ f + 1) = 1 → IsCyclic (Outer J)) := by
  have : Finite K := h.finite
  have : IsCyclic (K ≃+* K) :=
    CFSG.ComponentClassification.CatalogueSchreierLinearTwo.fieldAut_isCyclic K
  obtain ⟨⟨eT⟩, -, -, hout, -⟩ := unitary_full_diagonal_outer_order h hn hq
  obtain ⟨F, hF⟩ := exists_unitary_outer_field_factor h hn hq
  set T := primeFormP h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)
  have hfin : Finite (Outer T) := Nat.finite_of_card_ne_zero (by
    rw [hout]
    exact Nat.pos_iff_ne_zero.1 (Nat.mul_pos (Nat.mul_pos two_pos h.one_le)
      (Nat.gcd_pos_of_pos_right _ (Nat.succ_pos _))))
  set ι := (equivalence (e.trans eT.symm)).toMonoidHom.comp (outerCenterQuotientHom J)
  have hι : Function.Injective ι := outer_comp_injective J (e.trans eT.symm)
  have hmain : ∀ ℓ : ℕ, ℓ.Prime → ¬ ℓ ∣ Nat.gcd n (p ^ f + 1) →
      (∀ P : Sylow ℓ (Outer J), IsCyclic P) ∧ CFSG.pRank ℓ (Outer J) ≤ 1 := by
    intro ℓ hℓ hℓd
    have : Fact ℓ.Prime := ⟨hℓ⟩
    have hcop : Nat.Coprime (Nat.card F.ker) ℓ :=
      ((Nat.Prime.coprime_iff_not_dvd hℓ).2 fun h' => hℓd (h'.trans hF)).symm
    have hcyc : ∀ V : Subgroup (Outer J), IsPGroup ℓ V → IsCyclic V := fun V hV =>
      isCyclic_of_isPGroup_of_injective ι hι
        (fun W hW => isCyclic_of_isPGroup_of_ker_coprime F hcop hW) hV
    exact ⟨fun P => hcyc P P.isPGroup', pRank_le_one_of_forall_isCyclic hcyc⟩
  refine ⟨?_, hmain, fun hn3 ℓ hℓ hℓ5 => hmain ℓ hℓ fun hdvd => ?_, fun hd => ?_⟩
  · rw [← hout]
    exact Subgroup.card_dvd_of_injective ι hι
  · have h1 : ℓ ∣ 3 := hn3 ▸ hdvd.trans (Nat.gcd_dvd_left _ _)
    have h2 := Nat.le_of_dvd (by norm_num) h1
    omega
  ·
    have hinj : Function.Injective F := by
      rw [← MonoidHom.ker_eq_bot_iff, ← Subgroup.card_eq_one]
      rw [hd] at hF
      exact Nat.dvd_one.1 hF
    have : IsCyclic (Outer T) := isCyclic_of_injective F hinj
    exact isCyclic_of_injective ι hι

end CFSG.Quasithin.OuterPrimeControl
