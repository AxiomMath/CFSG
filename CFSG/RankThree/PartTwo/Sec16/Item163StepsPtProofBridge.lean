module

public import CFSG.RankThree.PartTwo.Sec16.Item163StepsPtProof
public import CFSG.RankThree.PartTwo.Sec15.Item1513StepsProofTools

public section

namespace CFSG.RankThree.PartTwo.Sec16

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec15

theorem step163MeetsPoint_of_step1513MeetsPoint (h : Sec15.Step1513MeetsPoint) :
    Step163MeetsPoint :=
  fun G _ _ A c L hR hJ Y hY => h G A c L hR hJ Y hY.prop

end CFSG.RankThree.PartTwo.Sec16
