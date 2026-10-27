module

public import CFSG.Quasithin.Vol2.KGFactC31J4M4
public import CFSG.Quasithin.Vol2.KGFactJ4M3KL
public import CFSG.Quasithin.Vol2.KGFactJ4M2Cent
public import CFSG.GH74.SmallRanks.AltM11
public import CFSG.LocalAnalysis.EvenSporadicStandard.J4Std.Interface
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.In23ExamKCover
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.In23ExamKDefs
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.In23ExamKQuot
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.In23FiveDefs
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.InA3Five
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.InS2Listed
public import CFSG.Quasithin.Background.B5NonInputs
public import CFSG.Quasithin.Background.F918M7
public import CFSG.Quasithin.Background.F918P2
public import CFSG.Quasithin.Background.FFC4Real
public import CFSG.Quasithin.Background.HPairBridge
public import CFSG.Quasithin.Background.SmithB51LnAut
public import CFSG.Quasithin.H13.J4Order
public import CFSG.Quasithin.Vol2.Ch12Sec1Lem1He
public import CFSG.Quasithin.Vol2.KGFactAutSylowSpor
public import CFSG.Quasithin.Vol2.KGFactC31A7
public import CFSG.Quasithin.Vol2.KGFactC31Ident
public import CFSG.Quasithin.Vol2.KGFactC31Rad
public import CFSG.RankThree.PartOne.S10.PlaneContract
public import CFSG.Sporadic.J4.QT2LocMain
public import CFSG.Sporadic.Schreier.J4SNoCompCover

public section

namespace CFSG.Quasithin.KGC31.J4

open CFSG.Open CFSG.QuasithinUnique CFSG.Blueprint CFSG.Quasithin.KGC31

theorem m3Facts :
    M3Facts CFSG.Quasithin.J4M3.KL CFSG.Quasithin.J4M3.hv0 :=
  ⟨CFSG.Quasithin.J4M3.centralizer_pCoreOf_M3_le, CFSG.Quasithin.J4M3.M3_maximal,
    CFSG.Quasithin.J4M3.KL_le_M3, CFSG.Quasithin.J4M3.M3_le_normalizer_KL,
    CFSG.Quasithin.J4M3.cComp_M3, CFSG.Quasithin.J4M3.pCoreOf_le_KL,
    CFSG.Quasithin.J4M3.KL_inf_centralizer, CFSG.Quasithin.J4M3.special_pCoreOf_M3,
    CFSG.Quasithin.J4M3.eSub_v0, CFSG.Quasithin.J4M3.KL_le_eNorm,
    CFSG.Quasithin.J4M3.surjective_eNHom_KL⟩

theorem inspC31SporadicAtJ_j4
    (hKW : CFSG.Quasithin.KGJ4.J4TwoLocalsKW)
    (hcard : Nat.card ↥CFSG.Quasithin.KGJ4.M4 = 10239344640) :
    CFSG.Quasithin.InspC31SporadicAtJ .J4 :=
  inspC31SporadicAtJ_j4_of' hKW CFSG.Quasithin.J4M2Core.centralizer_pCoreOf_M2_le m3Facts hcard

end CFSG.Quasithin.KGC31.J4

end
