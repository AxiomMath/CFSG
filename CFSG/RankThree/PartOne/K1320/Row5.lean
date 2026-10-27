module

public import CFSG.RankThree.PartOne.K1320.U
public import CFSG.RankThree.PartOne.K1320.FrameGen
public import CFSG.RankThree.PartOne.K1320.SU4Gen

public section

namespace CFSG.RankThree.PartOne.K1320

open CFSG CFSG.Assembly CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.GroupTheory
  CFSG.RankThree.PartOne CFSG.RankThree.PartOne.KFU
open CFSG.Assembly.LowTwoRank (StatedClassicalModel)

theorem row5Data_holds
    (hGA : CFSG.Open.GriessAllModelsStatement) : Row5Data := by
  intro G _ _ p A c L E f h hF hF13 hT hEA hf1 hpf hmodel
  obtain ⟨hZ, -, K, _, _, _, hK, ε, hε, r₀, r₁, hr₀, hr₀L, hr₁, hr₁L, -, -, -, hmap₀, hmap₁,
    hconj⟩ := KF132.kf132Row5_frame hGA h hF hF13 hEA hf1 hpf hmodel
  refine ⟨hZ, ?_⟩
  intro s hs hsL s' hs' hs'L hss'
  refine ⟨KF132.kf132Row5_dichotomy hGA h hF hF13 hEA hf1 hpf hmodel hs hsL hs' hs'L hss', ?_⟩
  have hp := h.prime
  have hp2 : p ≠ 2 := by
    have := Sec12Three.five_le h
    omega
  have hεinj : Function.Injective ε := by
    rw [← MonoidHom.ker_eq_bot_iff]
    exact eq_bot_iff.mpr (hε.central.trans hZ.le)
  have hq := isCentralPQuot_suQ (K := K) hp hp2 (by norm_num : 1 ≤ 4) hpf hf1 hK
  have hgen : kZero p E r₀ ⊔ kZero p E r₁ = L :=
    sup_eq_of_cover ε hεinj hε.surjective (suQ 4 hK) hq.surjective
      (kZero_le_of_reflection h hF13 hr₀ hr₀L) (kZero_le_of_reflection h hF13 hr₁ hr₁L)
      (suBlock_sup_suBlockB_eq_top hK hf1) hmap₀ hmap₁
  exact kZero_sup_of_pair hgen (hconj s hs hsL s' hs' hs'L hss')

theorem kf1320U'_holds
    (hGA : CFSG.Open.GriessAllModelsStatement)
    (hS : LocalAnalysis.ComponentInitial.SchreierFor InCatalog)
    (h133 : S13K.KF133Two) (hDist : S13K.KFCommDistinct)
    (hdist : RowModelsDistinct) (hThree : KF1320UThreeAt 4) : KF1320U' :=
  kf1320U'_of_inputs hGA hS h133 hDist hdist (row5Data_holds hGA) hThree

end CFSG.RankThree.PartOne.K1320
