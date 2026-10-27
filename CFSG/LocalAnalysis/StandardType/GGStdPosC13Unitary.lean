module

public import CFSG.Assembly.GL83LieDefs
public import CFSG.LocalAnalysis.StandardType.GGTableBRank
public import CFSG.LocalAnalysis.StandardType.GGNbrTableForms
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate117
import CFSG.LocalAnalysis.StandardType.GGStdPosC13PermConv
import CFSG.LocalAnalysis.StandardType.GGBstarDeltaUnitaryOutdiag
import CFSG.LocalAnalysis.StandardType.GGStdSubSmallRestUnitaryCenter
import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyUModel
import CFSG.LocalAnalysis.StandardType.GGNbrFrameOneUnitaryLabel
import CFSG.LocalAnalysis.StandardType.GGTableBUnitaryTorus
import CFSG.LocalAnalysis.StandardType.GGTableBUnitaryEndNodeInner
import CFSG.LocalAnalysis.StandardType.GGTableBTypeATorus

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

theorem recipeUnitary_reflGenW
    {d n p : ℕ} (hp : p.Prime) (hpq : p ∣ 2 ^ n + 1) (hn : 1 ≤ n)
    (hd : 3 ≤ d) (hdq : (d, 2 ^ n) ≠ (3, 2)) (hpd : ¬ p ∣ d) {Q : LargeEvenRawCont}
    (hQ : LargeEvenRecipeUnitary d (2 ^ n) Q) :
    LargeEvenRecipeUnitary d (2 ^ n) fun R _ I F =>
      Q R I F ∧ ∃ r, GGTorusLift p r R ∧ GGTorusReflGenW p r R I := by
  obtain ⟨K, _, _, hK, hQ⟩ := hQ
  refine ⟨K, inferInstance, inferInstance, hK, hQ, ?_⟩
  have hp2 : p ≠ 2 := TableBU.ne_two_of_dvd_two_pow_add_one hn hpq
  have := (TableBU.unitaryFieldData_of_card hK hn).charP
  exact ⟨0, TypeA.ggTorusLift_zero (two_dvd_card_statedProj_statedSU (by omega)),
    ggTorusReflGenW_of_permEltSC hp hp2 (TableBUE.center_proj_eq_bot hK hd hdq)
      (fun φ hφ hφp => InndiagSU.ggOutdiagPrime_unitary hK hn hd hdq hp hpq hpd φ hφ hφp)
      (StdSubRestU.ggCenterPrime_unitary hK hn hd hdq hp hp2 hpd)
      (UModel.ggTorusPermEltSC_unitary hK hn (by omega) hp hp2 hpq hpd)⟩

end CFSG.StandardType
