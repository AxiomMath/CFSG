module

public import CFSG.RankThree.PartOne.Mult.Trim
public import CFSG.RankThree.PartOne.MultRes.McL
public import CFSG.RankThree.PartOne.MultRes.Co1
public import CFSG.RankThree.PartOne.MultRes.Co2
public import CFSG.RankThree.PartOne.MultRes.Th
public import CFSG.RankThree.PartOne.MultRes.Suz
public import CFSG.RankThree.PartOne.MultRes.Co3
public import CFSG.RankThree.PartOne.MultRes.HN
public import CFSG.RankThree.PartOne.KS.LyScalCheck
public import CFSG.RankThree.PartOne.MultRes.ON
public import CFSG.RankThree.PartOne.MultRes.Co1Five

public section

namespace CFSG.RankThree.PartOne.MultRes

open CFSG.RankThree.PartOne.Mult

structure SporadicHardKernels : Prop where
  co1_five : SporadicKernelTrivial .Co1 5
  hn_five : SporadicKernelTrivial .HN 5
  ly_five : SporadicKernelTrivial .Ly 5

theorem sporadicResidualKernelsTrim_of_co1_seven
    (h : SporadicHardKernels) (h7 : SporadicKernelTrivial .Co1 7) :
    SporadicResidualKernelsTrim :=
  ⟨h.co1_five, h7, sporadicKernelTrivial_th_five, sporadicKernelTrivial_th_seven,
    sporadicKernelTrivial_co2_five, sporadicKernelTrivial_co3_five, sporadicKernelTrivial_mcl_five,
    sporadicKernelTrivial_suz_five, h.hn_five, h.ly_five, sporadicKernelTrivial_on_seven⟩

theorem sporadicResidualKernelsTrim_of_hard
    (h : SporadicHardKernels) : SporadicResidualKernelsTrim :=
  sporadicResidualKernelsTrim_of_co1_seven h sporadicKernelTrivial_co1_seven

theorem sporadicResidualKernelsTrim_of_co1_five
    (hco1 : SporadicKernelTrivial .Co1 5) : SporadicResidualKernelsTrim :=
  sporadicResidualKernelsTrim_of_hard
    ⟨hco1, sporadicKernelTrivial_hn_five, sporadicKernelTrivial_of_carrier KS.LyScal.lyKernelTrivial⟩

theorem sporadicResidualKernelsTrim_holds :
    SporadicResidualKernelsTrim :=
  sporadicResidualKernelsTrim_of_co1_five sporadicKernelTrivial_co1_five

end CFSG.RankThree.PartOne.MultRes
