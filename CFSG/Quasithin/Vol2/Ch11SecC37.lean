module

public import CFSG.Quasithin.Vol2.Ch11SecC37V7
public import CFSG.Quasithin.Vol2.Ch11SecC37J
public import CFSG.Quasithin.Vol2.Ch11SecC37B6

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecC

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13 CFSG.Quasithin.InternalSec
open scoped IsMulCommutative

theorem stmt11_3_7_of (h1102 : Stmt11_0_2) (h1104 : Stmt11_0_4) (h1122 : Stmt11_2_2)
    (h1134 : Stmt11_3_4) (h1135 : Stmt11_3_5) (h1136 : Stmt11_3_6) (h331 : Stmt3_3_1)
    (hC58 : TheoremC58) (h317 : AS317Sylow) (h3228 : Ch10.TmpL6_3_2_2_eight)
    (hG16 : ASInputs.AS_G_1_6) (h51 : AsB51) (hFC : SecB.FactCentralizerTwo)
    (hFC1 : SecB.FactFlagOneCentral) (hAS : FactAStarSylow) (hFPF : FactSL2NatFPF)
    (hF : SecA.NatFacts) (hSN : FactSL2SylowNormalizer) (hB : FactSL2Borel)
    (hBS : FactBorelOddSL3) (hBP : FactBorelOddSp4) (hKF : KindModuleFacts)
    (hTS : FactTorusLineSL3) (hTP : FactTorusLineSp4) (hTVS : FactTransvPointSL3)
    (hTVP : FactTransvPointSp4) : Stmt11_3_7 := by
  intro G _ _ T L I n V₁ H D g hyp hV₁ h31 hnot hAT hAC hD
  have s : Set37 T L I n V₁ H g := ⟨hyp, hV₁, h31, hnot, hAT, hAC⟩
  have i : Inp37 := ⟨h1102, h1104, h1122, h1134, h1135, h1136, h331, hG16, h51, hAS, hFPF, hF,
    hSN, hB, hBS, hBP, hKF, hTS, hTP, hFC1⟩
  have hJ := s.eq_commutator_thompsonJ hC58 h317 hFC h1102 h3228 h331
  have hG2 := hKF.2.2.2
  have hZL := s.Z_inf_centralizer_L hJ hG16 hAS hFPF hF h1102 hG2 h1122 h1104 h1134 h1135 h1136
    h331 hSN hB hD
  have hVL := s.fsuV_inf_centralizer_L hJ hG16 hAS hFPF hF h1102 hG2 h1122 h1104 h1134 h1135
    h1136 h331 hSN hB hD
  exact ⟨lemma11_3_7_one h1135 h1136 hyp hV₁ h31 hnot,
    d0Of_le h1104 h1134 h1135 h1136 hB hyp hJ hV₁ h31 hnot hAT hAC hD,
    ⟨hZL, hVL, s.VZ_inf_centralizer_K i hJ hD⟩, s.fsuV_eq_A i hTVS hTVP h3228 hVL,
    s.V₁_eq_commutator i hJ hD, s.exists_isCartanX_d0Of i hJ hD⟩

end CFSG.Quasithin.Vol2.Ch11.SecC
