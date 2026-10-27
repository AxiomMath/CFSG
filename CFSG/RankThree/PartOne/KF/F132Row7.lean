module

public import CFSG.RankThree.PartOne.KF.F132Core
public import CFSG.RankThree.PartOne.KF.R7Layer
public import CFSG.RankThree.PartOne.KF.F132AtEx
public import CFSG.RankThree.PartOne.KF.F132Center
public import CFSG.RankThree.PartOne.KFOUT3.KtyCore

public section

namespace CFSG.RankThree.PartOne.KF132

open CFSG CFSG.RankThree.PartOne CFSG.RankThree.PartOne.S13K CFSG.Assembly.LowTwoRank

theorem kf132AtEx_row7 (hGA : CFSG.Open.GriessAllModelsStatement) :
    KF132AtEx 7 := by
  intro G _ _ p A c L E h hF hF13 hT hr4 hrow hrA hr9
  have hEA : E = A := hrA (by norm_num)
  have hrow' := hrow
  obtain ⟨f, hf1, hpq, hmod⟩ := hrow
  have h5 := Sec12Three.five_le h
  have hf3 := three_le_of_dvd h5 hf1 hpq
  have hZL : Subgroup.center L = ⊥ := psp_two_center_trivial hGA hf1 hF.isQuasisimple_L hmod
  have hG : Sec12TwoGeneric p c L E := sec12TwoGeneric_of_center_bot hF hZL
  have hcL : c ∉ L := h.c_not_mem_of_generic hG
  have hcore : Table123Core p L (A ⊓ L) (E ⊓ L) := KFOUT3.table_core_of h hG
  obtain ⟨b, K, hd, hKmod⟩ := layerRow7_of_core h h.L_le_centralizer hG.E_eq hEA hcore hf1 hpq hmod
  obtain ⟨t, htL, hrefl, -, hKF, -⟩ := exists_reflection_of_core hGA h hEA hcL hd hf3 hKmod
  exact ⟨t, ⟨hrefl, L, hF13.inZeroStar, htL⟩, htL, f, f, ⟨hf1, hpq, hmod⟩, rfl, hKF⟩

end CFSG.RankThree.PartOne.KF132
