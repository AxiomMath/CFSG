module

public import CFSG.RankThree.PartOne.K1320.U5
public import CFSG.RankThree.PartOne.KF.F132Row6Qs

public section

namespace CFSG.RankThree.PartOne.K1320

open CFSG CFSG.Assembly CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.GroupTheory
  CFSG.RankThree.PartOne

theorem row6Data_holds
    (hGA : CFSG.Open.GriessAllModelsStatement) : Row6Data := by
  intro G _ _ p A c L E f h hF hF13 hT hEA hf1 hpf hmodel s hs hsL s' hs' hs'L hord
  exact KF132.kf132Row6_dichotomy hGA h hF hF13 hEA hf1 hpf hmodel hs hsL hs' hs'L hord

theorem row6Lift_holds
    (hGA : CFSG.Open.GriessAllModelsStatement) : Row6Lift := by
  intro G _ _ p A c L E f h hF hF13 _ hEA hf1 hpf hmodel s hs hsL hexc
  obtain ⟨Kt, hKt⟩ := KF132.kf132Row6_kfKt hGA KF132.kfK0 h hF hF13 hEA hf1 hpf hmodel s hs hsL hexc
  have hm := S13K.isQuasisimple_and_center_of_model_psl_two hKt.2.2.1
  exact ⟨Kt, ⟨hKt.1, hm.1, hm.2, hKt.2.2.2.2.1, hKt.2.2.2.2.2⟩,
    KF132.kf132Row6_exc_quasisimple hGA h hF hF13 hEA hf1 hpf hmodel s hs hsL hexc⟩

theorem kf1320U5'_holds
    (hGA : CFSG.Open.GriessAllModelsStatement)
    (hS : LocalAnalysis.ComponentInitial.SchreierFor InCatalog) (h133 : S13K.KF133Two)
    (hdist : RowModelsDistinct) (hThree : KF1320UThreeAt 5) : KF1320U5' :=
  kf1320U5'_of_inputs hGA hS h133 hdist (row6Data_holds hGA) (row6Lift_holds hGA) hThree

end CFSG.RankThree.PartOne.K1320
