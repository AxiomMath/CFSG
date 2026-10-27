module

public import CFSG.LocalAnalysis.StandardType.GGNbrTableForms
import CFSG.LocalAnalysis.StandardType.GGStdPosC24Signed
import CFSG.LocalAnalysis.StandardType.GGStdPosC24HypDescent
import CFSG.LocalAnalysis.StandardType.GGNbrFieldOtherClassicalUnitHypLift

public section

namespace CFSG.StandardType

open CFSG.Assembly

theorem largeEvenLabelAll_reflGenW_unitaryHyp
    {p : ℕ} (hp : p.Prime)
    {lab : LargeEvenLabel} (hlab : LargeEvenInLambda2 lab)
    (h : lab.tag = .twA ∧ lab.rank = 5 ∧ p ∣ 2 ^ lab.n - 1) :
    LargeEvenLabelAll lab fun R _ I _ => ∃ r, GGTorusLift p r R ∧ GGTorusReflGenW p r R I := by
  obtain ⟨t, l, n⟩ := lab
  obtain ⟨ht, hl, hpq⟩ := h
  dsimp only at ht hl hpq
  subst ht hl
  have hn : 1 ≤ n := hlab.1
  have hp2 : p ≠ 2 := by
    rintro rfl
    have h1 : 2 ∣ 2 ^ n := dvd_pow_self 2 (by omega)
    have h2 : 1 ≤ 2 ^ n := Nat.one_le_two_pow
    omega
  have hpq' : ¬ p ∣ 2 ^ n + 1 := not_dvd_two_pow_add_one_of_dvd_sub_one hp hp2 hpq
  have hq4 : 4 ≤ 2 ^ n := four_le_two_pow_of_dvd_sub_one hp hp2 hn hpq
  intro Q hQ
  dsimp only [LargeEvenRawDatum] at hQ ⊢
  obtain ⟨K, _, _, hK, hQ'⟩ := hQ
  refine ⟨K, inferInstance, inferInstance, hK, hQ', 3, ggTorusLift_unitaryHypSix hK hn hp hp2 hpq,
    ggTorusReflGenW_of_signedEltSC hp hp2 (center_statedProj_statedSU_eq_bot hK (by norm_num))
      (fun φ hφ hφp => NbrInnerMore.ggOutdiagPrime_unitary_of_not_dvd hK hn (by omega)
        (by omega) hp hpq' φ hφ hφp)
      (ggCenterPrime_psu_even hK (by decide) (by norm_num) hq4 hpq')
      (ggTorusSignedEltSC_statedProj_hyp (TableBU.unitaryFieldData_of_card hK hn) hp hp2 hpq)⟩

end CFSG.StandardType

end
