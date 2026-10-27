module

public import CFSG.RankThree.PartOne.S13K.Row1At
public import CFSG.RankThree.PartOne.S13K.Comm134

public section

namespace CFSG.RankThree.PartOne.S13K

open CFSG CFSG.Assembly CFSG.RankThree.PartOne CFSG.Assembly.LowTwoRank

theorem kfLiftRowOne_holds (hGA : CFSG.Open.GriessAllModelsStatement) :
    KFLiftRowOne := by
  intro G _ _ p A c L E h hF hEA hrow t ht htL
  obtain ⟨f, hf1, hpf, hmodel⟩ := hrow
  exact KFAt.toLiftAt (kfAt_row1 hGA h hF hEA hpf hf1 hmodel t ht htL)

theorem kf141a_holds (hGA : CFSG.Open.GriessAllModelsStatement) :
    KF141a := by
  intro G _ _ p A c L E f hH hF _ _ hf hpq hmodel hEA _ t ht htL
  exact kfAt_row1 hGA hH hF hEA hpq hf hmodel t ht htL

theorem kf132At_row1 (hGA : CFSG.Open.GriessAllModelsStatement) :
    KF132At 1 := by
  intro G _ _ p A c L E h hF _ _ _ hrow hEA _ t ht htL
  obtain ⟨f, hf1, hpf, hmodel⟩ := hrow
  exact ⟨f, f, ⟨hf1, hpf, hmodel⟩, rfl,
    kfAt_row1 hGA h hF (hEA (by norm_num)) hpf hf1 hmodel t ht htL⟩

end CFSG.RankThree.PartOne.S13K
