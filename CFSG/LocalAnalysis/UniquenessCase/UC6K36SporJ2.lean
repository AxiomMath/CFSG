module

public import CFSG.LocalAnalysis.UniquenessCase.UC6K36SporM12
public import Certificates.Certificate36153
public import CFSG.LocalAnalysis.ComponentClassification.J2CoverAutOddCore
public import CFSG.Sporadic.J2
public import CFSG.Sporadic.Schreier.PairJ2Faithful

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UCK

open CFSG.Open Subgroup CFSG.Blueprint
open CFSG.PSL3Four.Native CFSG.ComponentClassification.PSL3Four Certificates.K36Spor
open CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.PairNative

namespace Spor

theorem center_eq_bot_of_mulEquiv {X Y : Type*} [Group X] [Group Y] (e : X ≃* Y)
    (h : Subgroup.center Y = ⊥) : Subgroup.center X = ⊥ := by
  rw [eq_bot_iff]
  intro z hz
  have hz' : e z ∈ Subgroup.center Y := by
    rw [Subgroup.mem_center_iff] at hz ⊢
    intro g
    obtain ⟨g', rfl⟩ := e.surjective g
    rw [← map_mul, ← map_mul, hz g']
  rw [h, Subgroup.mem_bot] at hz'
  exact Subgroup.mem_bot.2 (e.injective (hz'.trans (map_one e).symm))


theorem planeGenOrExc_j2P {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) : PlaneGenOrExc ↥j2P p := by
  have hZ : Subgroup.center ↥j2P = ⊥ :=
    center_eq_bot_of_mulEquiv (j2PermEquiv.symm.trans CFSG.ComponentClassification.J2Cover.nativeEquivP)
      CFSG.ComponentClassification.J2Cover.center_P
  have hcard : Nat.card ↥j2P = 604800 := by
    rw [← Nat.card_congr j2PermEquiv.toEquiv, CFSG.Sporadic.J2.card_J2]
  have hA : Nat.card (MulAut ↥j2P) ≤ 2 * Nat.card ↥j2P := by
    rw [Nat.card_congr (MulAut.congr j2PermEquiv.symm).toEquiv, CFSG.ComponentClassification.J2Cover.j2_mulAut_card,
      ← Nat.card_congr j2PermEquiv.toEquiv]
  have hinner : ∀ ε : MulAut ↥j2P, ε ^ p = 1 → ε ∈ (MulAut.conj : ↥j2P →* MulAut ↥j2P).range :=
    fun ε hε => mem_range_conj_of_card_mulAut_le hZ hA (hp.odd_of_ne_two hp2) ε hε
  by_cases hp3 : p = 3
  · subst hp3
    have hfac : (Nat.card ↥j2P).factorization 3 = 3 := by
      rw [hcard]
      exact factorization_eq_of_dvd Nat.prime_three (by norm_num) (by norm_num) (by norm_num)
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    obtain ⟨E, hEc, hE⟩ := Certificates.certificate36153.1
    exact planeGenOrExc_of_planeOK hZ hinner (planeOK_of_sylow (Sylow.ofCard E (by rw [hEc, hfac]; norm_num))
      fun A hA hAe hAc => Or.inl (hE A hA hAe (hAc.trans (by norm_num))))
  by_cases hp5 : p = 5
  · subst hp5
    have hfac : (Nat.card ↥j2P).factorization 5 = 2 := by
      rw [hcard]
      exact factorization_eq_of_dvd (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
    obtain ⟨E, hEc, hE⟩ := Certificates.certificate36153.2
    exact planeGenOrExc_of_planeOK hZ hinner (planeOK_of_sylow (Sylow.ofCard E (by rw [hEc, hfac]; norm_num))
      fun A hA hAe hAc => Or.inl (hE A hA hAe (hAc.trans (by norm_num))))
  · refine planeGenOrExc_of_not_dvd hZ hinner ?_
    rw [hcard]
    intro h
    have h' : p ^ 2 ∣ 175 := sq_dvd_of_sq_dvd_two_three hp hp2 hp3 (a := 7) (b := 3) (by simpa using h)
    have hle : p ^ 2 ≤ 175 := Nat.le_of_dvd (by norm_num) h'
    have hp13 : p ≤ 13 := by nlinarith
    interval_cases p <;> revert hp hp2 hp3 hp5 h' <;> decide

theorem planeGenOrExc_J2 {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) : PlaneGenOrExc NativeSporadic.J2 p :=
  planeGenOrExc_of_mulEquiv j2PermEquiv.symm (planeGenOrExc_j2P hp hp2)

end Spor

end CFSG.LocalAnalysis.UniquenessCase.UCK
