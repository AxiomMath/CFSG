module

public import CFSG.RankThree.PartTwo.Sec21.HeringSec23Assembly
public import CFSG.RankThree.PartTwo.Sec21.FF81Assembly
public import CFSG.RankThree.PartTwo.Sec21.FF81FS79Prop2K
public import CFSG.GF2Type.Smith1979CharTwoKPHolds

public section

namespace CFSG.RankThree.PartTwo.Sec21

theorem item233_of_ff81aProp1
    (hP1 : FF81.KF_FF81aProp1) (hGF : CFSG.RankThree.GF2n.GF2nTypeStatement) : Item233 :=
  item233_of_ff81TheoremA (FF81.ff81TheoremAK_of_items_cited ⟨FF81.kf_fs79Prop2K, hP1⟩) hGF
    CFSG.GF2Type.smith1979CharTwoKP_holds

theorem item231_of_ff81aProp1
    (hP1 : FF81.KF_FF81aProp1) (hGF : CFSG.RankThree.GF2n.GF2nTypeStatement) : Item231 :=
  item231_of_ff81TheoremA (FF81.ff81TheoremAK_of_items_cited ⟨FF81.kf_fs79Prop2K, hP1⟩) hGF
    CFSG.GF2Type.smith1979CharTwoKP_holds

end CFSG.RankThree.PartTwo.Sec21
