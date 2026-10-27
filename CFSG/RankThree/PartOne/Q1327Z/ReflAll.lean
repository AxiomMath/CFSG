module

public import CFSG.RankThree.PartOne.Q1327Z.Final
public import CFSG.RankThree.PartOne.Q1327Z.ReflOm8
public import CFSG.RankThree.PartOne.Q1327Z.ReflSp6Split
public import CFSG.RankThree.PartOne.Q1327Z.Row10
public import CFSG.RankThree.PartOne.Q1327Z.Row10Frame

public section

namespace CFSG.RankThree.PartOne.Q1327Z

open CFSG CFSG.Assembly CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.GroupTheory
  CFSG.RankThree.PartOne CFSG.RankThree.PartOne.S13K CFSG.RankThree.PartOne.K1320
  CFSG.RankThree.PartOne.K1327 CFSG.RankThree.PartOne.KFU CFSG.RankThree.PartOne.Q1327
  CFSG.RankThree.PartOne.Q1327C CFSG.RankThree.PartOne.Q1327T
open CFSG.Assembly.LowTwoRank (StatedClassicalModel)
open CFSG.LocalAnalysis.ComponentInitial (SchreierFor)

theorem kf1327Refl_holds : KF1327Refl := by
  intro G _ _ p X A₀ F h ho t ht hrefl c₀ hc₀ hc₀1
  rcases ho with h10 | hsp | hom
  · exact refl_row10_of_model (fun K _ _ _ p hp hp5 hpq => noncommOK_T10 hp hp5 hpq) h h10 ht
      hrefl hc₀ hc₀1
  · exact refl_sp6split h hsp ht hrefl hc₀ hc₀1
  · exact refl_om8 h hom ht hrefl hc₀ hc₀1

theorem kf1327Q_of_inspection
    (hGA : CFSG.Open.GriessAllModelsStatement)
    (hS : SchreierFor InCatalog) (hRe : Sec13Reinst) (hTwo : TwoActionInputs)
    (hFull : K156.Full106Stmt) (hSLB : N143.SectionListBound) (hI613 : N143.Item613ListIdx)
    (hBridge : N143.EvenListBridge) (hP5 : KF1327P5) (hB : KF1327BM) (hI : Row8U3Inspection) :
    K1327.KF1327Q :=
  kf1327Q_of_remR hGA hS hRe hTwo hFull hSLB hI613 hBridge hP5 hB ⟨hI, kf1327Refl_holds⟩

end CFSG.RankThree.PartOne.Q1327Z
