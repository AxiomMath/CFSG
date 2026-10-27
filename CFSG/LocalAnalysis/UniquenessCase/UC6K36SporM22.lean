module

public import CFSG.LocalAnalysis.UniquenessCase.UC6K36SporM12
public import Certificates.Certificate36152
public import CFSG.Sporadic.Schreier.MathieuOddCoreM22

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UCK

open CFSG.Open Subgroup CFSG.Blueprint
open CFSG.PSL3Four.Native CFSG.ComponentClassification.PSL3Four Certificates.K36Spor

namespace Spor

theorem planeGenOrExc_M22 {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    PlaneGenOrExc ↥NativeSporadic.M22 p := by
  have hZ : Subgroup.center ↥NativeSporadic.M22 = ⊥ := CFSG.Sporadic.Schreier.m22_center_eq_bot'
  have hcard : Nat.card ↥NativeSporadic.M22 = 443520 := CFSG.Sporadic.Schreier.m22_card
  have hinner : ∀ ε : MulAut ↥NativeSporadic.M22, ε ^ p = 1 →
      ε ∈ (MulAut.conj : ↥NativeSporadic.M22 →* MulAut ↥NativeSporadic.M22).range :=
    fun ε hε => mem_range_conj_of_card_mulAut_le hZ CFSG.Sporadic.Schreier.m22_mulAut_card
      (hp.odd_of_ne_two hp2) ε hε
  by_cases hp3 : p = 3
  · subst hp3
    have hfac : (Nat.card ↥NativeSporadic.M22).factorization 3 = 2 := by
      rw [hcard]
      exact factorization_eq_of_dvd Nat.prime_three (by norm_num) (by norm_num) (by norm_num)
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    obtain ⟨E, hEc, hE⟩ := Certificates.certificate36152
    exact planeGenOrExc_of_planeOK hZ hinner (planeOK_of_sylow (Sylow.ofCard E (by rw [hEc, hfac]; norm_num))
      fun A hA hAe hAc => Or.inl (hE A hA hAe (hAc.trans (by norm_num))))
  · refine planeGenOrExc_of_not_dvd hZ hinner ?_
    rw [hcard]
    intro h
    have h' : p ^ 2 ∣ 385 := sq_dvd_of_sq_dvd_two_three hp hp2 hp3 (a := 7) (b := 2) (by simpa using h)
    have hle : p ^ 2 ≤ 385 := Nat.le_of_dvd (by norm_num) h'
    have hp19 : p ≤ 19 := by nlinarith
    interval_cases p <;> revert hp hp2 hp3 h' <;> decide

end Spor

end CFSG.LocalAnalysis.UniquenessCase.UCK
