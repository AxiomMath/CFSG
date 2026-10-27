module

public import CFSG.Quasithin.Vol2.Ch8Sec2L822Kz3Lz
public import CFSG.Quasithin.Vol2.Ch8Sec2L822R4
public import CFSG.Quasithin.Vol2.Ch8Sec2L822Kz3Steps
public import CFSG.Quasithin.Vol2.Ch12Sec2Action
public import CFSG.Quasithin.Vol2.Ch8Sec2L822KzHeBranch

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Quasithin.E3 CFSG.Quasithin.H CFSG.Quasithin.ASInputs CFSG.Quasithin
  CFSG.Quasithin.H13.L319 CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank
  CFSG.Quasithin.EmptyFaithfulMultiple
open scoped IsMulCommutative

theorem res822Kz_holds' (h134 : EmptyFaithfulMultiple.Prop134E9He) (h711n : Stmt7_1_1_normal)
    (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h39 : A39ForSQTK) (h3228 : Stmt3_2_2_eight)
    (hC58 : TheoremC58) (h317 : AS317Sylow)
    (hM11 : M11Sub144O2_kz) (hHe : HeSubO2_kz) (hHeA : HeAutInner_kz2)
    (hN1 : KzM22Sub5760_kz3) (hN2 : KzM22Cover17280_kz3) (hN3 : KzCodeHexad5760_kz3)
    (hAut : KzAutE9Perfect_kz3) (h312 : CFSG.QuasithinUnique.Vol2Native.A312ForSQTKCat)
    (hF : A318Facts) (h36 : A36ForSQTK) :
    Res822Kz := by
  intro G _ _ T L I hyp h731 h821 hc hrow hrowM hnot H hH hVH hXi ⟨φ, hφs, hφk⟩
  obtain ⟨z, hz1, hzV, hzΩ, hHz, hTz, P, hPX, hP3, hPcard, hcon⟩ :=
    exists_z_prop134_kz h134 hyp h731 h821 hrow h711n h37 h38 h39 h3228 hC58 h317 hH hVH φ hφs hφk
  have hrel : (pCoreOf 2 (twoResidual H)).relIndex (twoResidual H) = 9 := by
    rw [F6.twoResidual_eq_oTwoUpper H]
    exact relIndex_oTwoUpper_eq_nine_kz φ hφs hφk
  have hLz : KzLzInput_kz2 :=
    kzLzInput_kz2_holds h711n h3228 (res822ThreeCover_holds' h3228 h711n hF h36 h38) hN1 hN2 hN3
  obtain ⟨Lz, hLzG, hLzT, hLzF, hA6, hH6⟩ :=
    hLz G T L I hyp h731 h821 hc hrow hrowM hnot H hH hVH z hz1 hzV hzΩ hHz hTz
  obtain ⟨K, hKG, hTK, hXK, hcase⟩ :=
    kzStepsRel_kz3_holds h37 h38 h39 h312 hAut h3228 G T L I hyp h731 h821 hc hrow hrowM hnot H hH hVH
      hXi hrel z P Lz hz1 hzV hzΩ hHz hTz hPX hP3 hPcard hcon hLzG hLzT hLzF hA6 hH6
  have hT : IsSylowTwoOf T (Subgroup.centralizer ({z} : Set G)) :=
    isSylowTwoOf_of_quasithinIsSylowTwo hyp.fsu.sylow hTz
  have hTH : T ≤ H := hH.1.1
  have hXH : twoResidual H ≤ H := by
    rw [F6.twoResidual_eq_oTwoUpper H]
    exact oTwoUpper_le H
  obtain ⟨-, hTX, -, p, -, -, -, -, hirr⟩ := hXi
  rcases hcase with hM | ⟨Bq, hHe', hBq, hBqp, hBqT⟩
  · exact false_of_m11_K_kz2 hM11 φ hφs hφk hT hTH hKG hTK hXH hXK hPX hP3 hPcard hM
  · exact false_of_he_K_kz2 hHeA hHe hT hKG hTK hXK hTX hrel hirr hHe' Bq hBq hBqp hBqT

end CFSG.Quasithin.H13
