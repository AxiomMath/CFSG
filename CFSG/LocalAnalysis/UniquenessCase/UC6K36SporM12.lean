module

public import Certificates.Data.K36SporPlanes
public import Certificates.Certificate36151
public import CFSG.Sporadic.Schreier.MathieuOddCoreM12
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.ComponentClassification.PSL3FourActionData

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UCK

open CFSG.Open Subgroup CFSG.Blueprint
open CFSG.PSL3Four.Native CFSG.ComponentClassification.PSL3Four Certificates.K36Spor

namespace Spor

theorem factorization_eq_of_dvd {n p k : ℕ} (hp : p.Prime) (hn : n ≠ 0) (h1 : p ^ k ∣ n)
    (h2 : ¬ p ^ (k + 1) ∣ n) : n.factorization p = k := by
  have hle := (hp.pow_dvd_iff_le_factorization hn).1 h1
  have hlt : ¬ k + 1 ≤ n.factorization p := fun h => h2 ((hp.pow_dvd_iff_le_factorization hn).2 h)
  omega

theorem sq_dvd_of_sq_dvd_two_three {p a b m : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hp3 : p ≠ 3)
    (h : p ^ 2 ∣ 2 ^ a * 3 ^ b * m) : p ^ 2 ∣ m := by
  have hc2 : Nat.Coprime (p ^ 2) (2 ^ a) :=
    Nat.Coprime.pow _ _ ((Nat.coprime_primes hp Nat.prime_two).2 hp2)
  have hc3 : Nat.Coprime (p ^ 2) (3 ^ b) :=
    Nat.Coprime.pow _ _ ((Nat.coprime_primes hp Nat.prime_three).2 hp3)
  have hc : Nat.Coprime (p ^ 2) (2 ^ a * 3 ^ b) := Nat.Coprime.mul_right hc2 hc3
  rw [mul_comm] at h
  exact hc.dvd_of_dvd_mul_right h

theorem planeGenOrExc_M12 {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    PlaneGenOrExc ↥NativeSporadic.M12 p := by
  have hZ : Subgroup.center ↥NativeSporadic.M12 = ⊥ := CFSG.Sporadic.Schreier.m12_center_eq_bot'
  have hcard : Nat.card ↥NativeSporadic.M12 = 95040 := CFSG.Sporadic.Schreier.m12_card
  have hinner : ∀ ε : MulAut ↥NativeSporadic.M12, ε ^ p = 1 →
      ε ∈ (MulAut.conj : ↥NativeSporadic.M12 →* MulAut ↥NativeSporadic.M12).range :=
    fun ε hε => mem_range_conj_of_card_mulAut_le hZ CFSG.Sporadic.Schreier.m12_mulAut_card
      (hp.odd_of_ne_two hp2) ε hε
  by_cases hp3 : p = 3
  · subst hp3
    have hfac : (Nat.card ↥NativeSporadic.M12).factorization 3 = 3 := by
      rw [hcard]
      exact factorization_eq_of_dvd Nat.prime_three (by norm_num) (by norm_num) (by norm_num)
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    obtain ⟨E, hEc, hE⟩ := Certificates.certificate36151
    exact planeGenOrExc_of_planeOK hZ hinner (planeOK_of_sylow (Sylow.ofCard E (by rw [hEc, hfac]; norm_num))
      fun A hA hAe hAc => hE A hA hAe (hAc.trans (by norm_num)))
  · refine planeGenOrExc_of_not_dvd hZ hinner ?_
    rw [hcard]
    intro h
    have h' : p ^ 2 ∣ 55 := sq_dvd_of_sq_dvd_two_three hp hp2 hp3 (a := 6) (b := 3) (by simpa using h)
    have hle : p ^ 2 ≤ 55 := Nat.le_of_dvd (by norm_num) h'
    have hp7 : p ≤ 7 := by nlinarith
    interval_cases p <;> revert hp hp2 hp3 h' <;> decide

end Spor

end CFSG.LocalAnalysis.UniquenessCase.UCK
