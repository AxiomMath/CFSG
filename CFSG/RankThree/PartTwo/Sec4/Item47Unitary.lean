module

public import CFSG.RankThree.PartTwo.Sec4.Item47CasesEven
import CFSG.HardMathSupport.Timmesfeld.LinearRank.UnitaryDiagonal

public section

namespace CFSG.RankThree.PartTwo.Sec4

open CFSG CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.LocalAnalysis.ComponentInitial (UnitaryFieldData)
open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner equivalence)
open CFSG.Assembly.RankThreeEven (projSU)

variable {p f : ℕ} {K : Type} [Field K] {n : ℕ}

theorem isPrimeFormGram_one_GL : IsPrimeFormGram (1 : GL (Fin n) K) :=
  CFSG.HardMathSupport.Timmesfeld.LinearRank.isPrimeFormGram_one

theorem card_outer_primeFormP_dvd [Finite K] (h : UnitaryFieldData p f K) (hn : 3 ≤ n)
    (hq : ¬(n = 3 ∧ p ^ f = 2)) :
    Nat.card (Outer (primeFormP h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K))) ∣
      2 * f * (p ^ f + 1) := by
  classical
  have hC : IsPrimeFormGram (1 : GL (Fin n) K) := isPrimeFormGram_one_GL
  obtain ⟨-, -, -, -, -, hff, hsurj, hker, -, hinner, hdvd⟩ :=
    unitary_prime_form_full_semilinear_realization h hC hn hq
  set P := primeFormP h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)
  set ψ := primeFormFieldFactor h hC hn hq
  set D := primeFormD h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)
  have hInnD : inner P ≤ D := by
    intro α hα
    obtain ⟨s, rfl⟩ := (hinner α).mp hα
    rw [← hker, MonoidHom.mem_ker]
    have := hff ⟨s, s.2.1⟩ 1
    rwa [map_one, mul_one] at this
  have hAut : Nat.card (MulAut P) = Nat.card (K ≃+* K) * Nat.card D := by
    rw [← hker, ← Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective ψ hsurj).toEquiv]
    exact Subgroup.card_eq_card_quotient_mul_card_subgroup _
  have hD : Nat.card D = Nat.card (D ⧸ (inner P).subgroupOf D) * Nat.card (inner P) := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup ((inner P).subgroupOf D),
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hInnD).toEquiv]
  have hOut : Nat.card (MulAut P) = Nat.card (Outer P) * Nat.card (inner P) :=
    Subgroup.card_eq_card_quotient_mul_card_subgroup _
  have hfK : Nat.card (K ≃+* K) = 2 * f :=
    (CFSG.LocalAnalysis.ComponentInitial.card_ringAut_and_isCyclic h.prime K h.card).1
  have hInn : 0 < Nat.card (inner P) := Nat.card_pos
  have heq : Nat.card (Outer P) = 2 * f * Nat.card (D ⧸ (inner P).subgroupOf D) := by
    have h1 := hOut.symm.trans (hAut.trans (by rw [hD, hfK]))
    rw [← mul_assoc] at h1
    exact Nat.eq_of_mul_eq_mul_right hInn h1
  rw [heq]
  exact Nat.mul_dvd_mul_left _ hdvd

theorem card_outer_projSU_dvd (n p f : ℕ) [Fact p.Prime] (hf : 1 ≤ f) (hn : 3 ≤ n)
    (hq : ¬(n = 3 ∧ p ^ f = 2)) : Nat.card (Outer (projSU n p f)) ∣ 2 * f * (p ^ f + 1) := by
  have hU := unitaryFieldData_galoisField p f hf
  have hC : IsPrimeFormGram (1 : GL (Fin n) (GaloisField p (2 * f))) := isPrimeFormGram_one_GL
  obtain ⟨⟨e₃⟩, -⟩ := unitary_prime_form_full_semilinear_realization hU hC hn hq
  have e : projSU n p f ≃* primeFormP hU
      ((1 : GL (Fin n) (GaloisField p (2 * f))) : Matrix (Fin n) (Fin n) _) :=
    (projSUEquivStatedProj n p f).trans ((unitaryPSUEquiv hU (by omega)).symm.trans e₃.symm)
  rw [Nat.card_congr (equivalence e).toEquiv]
  exact card_outer_primeFormP_dvd hU hn hq

theorem outU43_holds : ¬ 3 ∣ Nat.card (Outer (projSU 4 3 1)) := fun h3 => by
  have := h3.trans (card_outer_projSU_dvd 4 3 1 le_rfl (by norm_num) (by norm_num))
  norm_num at this

theorem outU54_holds : ¬ 3 ∣ Nat.card (Outer (projSU 5 2 2)) := fun h3 => by
  have := h3.trans (card_outer_projSU_dvd 5 2 2 (by norm_num) (by norm_num) (by norm_num))
  norm_num at this

theorem outU4p_holds : ∀ (p : ℕ) [Fact p.Prime], 3 < p → p % 3 = 1 →
    ¬ 3 ∣ Nat.card (Outer (projSU 4 p 1)) := by
  intro p _ hp3 hp1 h3
  have := h3.trans (card_outer_projSU_dvd 4 p 1 le_rfl (by norm_num) (by omega))
  rw [pow_one] at this
  omega

end CFSG.RankThree.PartTwo.Sec4
