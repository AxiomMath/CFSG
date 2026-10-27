module

public import CFSG.RankThree.PartOne.K159R5.RowFiveSyl
public import CFSG.RankThree.PartOne.K159R5.L0cFive

public section

namespace CFSG.RankThree.PartOne.K159R5

open CFSG CFSG.RankThree.PartOne CFSG.RankThree.PartOne.S15K

theorem kf158BlocksFiveSyl_of_layerRowFiveS (hL : LayerRowFiveS) : KF158BlocksFiveSyl := by
  intro G _ _ p A c L E h15 hF hout b hb hb1 Y hY0 hYb hYI
  have hp := h15.h12.prime
  obtain ⟨ι, Q, hQH, hQc, hperf, -, hQs⟩ := hL G p A c L E h15 hF hout b hb hb1
  have hYC : Y ≤ Subgroup.centralizer ({b} : Set G) := (mem_thetaComponentsAt_iff.mp hYb).1
  obtain ⟨i, rfl⟩ := eq_component_of_mem_thetaComponentsAt_of_perfect hp inf_le_right Q hQH hQc
    hperf hYb (le_inf hYI hYC)
  exact hQs i

theorem kf158L0cRowFive_of_layerRowFiveS (hL : LayerRowFiveS) : KF158L0cRowFive :=
  kf158L0cRowFive_of_sylAb (fun G _ _ p A c L E h15 hF hout => (hL G p A c L E h15 hF hout).toW)
    (kf158BlocksFiveSyl_of_layerRowFiveS hL)

theorem kf158L0cRowFive_of_package (hMod : KFU5Mod) (hAt : KFU5At) (h5 : U5FiveInndiag) :
    KF158L0cRowFive :=
  kf158L0cRowFive_of_layerRowFiveS (layerRowFiveS_of_package hMod hAt h5)

end CFSG.RankThree.PartOne.K159R5
