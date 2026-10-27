module

public import CFSG.RankThree.PartTwo.Sec15.Gagen1515FpfMain
public import CFSG.RankThree.PartTwo.Sec14.Ronan148QDefs
import CFSG.RankThree.PartTwo.Sec15.Liebeck1515C3

public section

namespace CFSG.RankThree.PartTwo.Sec15.Gagen1515Fpf

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14

section Certs


theorem case3Fpf_of (h134 : Item134) (h48 : Sec4.Item4_8) (h45 : Sec4.Item4_5)
    (h143 : Ronan148Q.Item143QS14) : Case3Fpf :=
  fun _ _ _ _ _ _ _ h hΩB _ _ hTX hT hTT₀ hT₀ hAT₀ hY =>
    Liebeck1515.not_case148Three h134 h48 h45 h143 h hΩB hTX hT hTT₀ hT₀ hAT₀ hY

theorem step1515HJEndFpfRBoundOff_holds (hbal : Step143Balance)
    (h134 : Item134) (h48 : Sec4.Item4_8) (h45 : Sec4.Item4_5) (h143 : Ronan148Q.Item143QS14)
    (h142 : Item142R) (hc142 : Concl142R) (h146 : Item146S14) (h148 : Item148R)
    (h152 : Item152R) (h153 : Item153MainR) (h1411 : Item1411_1R) :
    Step1515HJEndFpfRBoundOff :=
  step1515HJEndFpfRBoundOff_of hbal h134 h48 h142 hc142 h146 h148 h152 h153 h1411
    (case3Fpf_of h134 h48 h45 h143)

end Certs

end CFSG.RankThree.PartTwo.Sec15.Gagen1515Fpf
