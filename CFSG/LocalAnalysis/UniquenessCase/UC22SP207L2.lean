module

public import CFSG.LocalAnalysis.UniquenessCase.UC22SP207Defs
import CFSG.LocalAnalysis.UniquenessCase.UC22SP207Coxeter
import CFSG.LocalAnalysis.UniquenessCase.UC22SP207Datum
import CFSG.LocalAnalysis.UniquenessCase.UC22SP207Transfer
import CFSG.Milestones.ASVolI.I2

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.ASVolI.ChIJK CFSG.LieType.Universal Matrix

theorem uc22sp207_hasCentralLongest_L2 {X : Type} [Group X] {n : ℕ} (h : IsL2 X n) :
    HasCentralLongest X := by
  obtain ⟨⟨hp, hf, -, -⟩, K, hKf, hKfin, hcard, ⟨e⟩⟩ :=
    CFSG.Blueprint.LieModel.statedClassicalModel h (by decide)
  have : Fact (Nat.Prime 2) := ⟨hp⟩
  have : CharP K 2 := burnsideI2BN_charP_of_card hp hf hcard
  have hsub : Subsingleton (Fin (SpecialLinear.rootDatum 1 K).rank) :=
    inferInstanceAs (Subsingleton (Fin 1))
  have hSL : HasCentralLongest (SpecialLinearGroup (Fin 2) K) :=
    uc22sp207_hasCentralLongest_of_datum (D := SpecialLinear.rootDatum 1 K)
      (n := SpecialLinear.weylRep 1 K) (H := SpecialLinear.torus 1 K)
      (SpecialLinear.isCTGroupDatum 1 K) (SpecialLinear.steinbergExtras 1 K)
      CFSG.StandardType.GGRootSL.bruhatExtras burnsideI2BN_SL_isPGroup
      (burnsideI2BN_SL_torus hp (hcard ▸ dvd_pow_self 2 (by omega : n ≠ 0)))
      (uc22sp207_exists_central_longest_of_subsingleton _)
  let eSL : SpecialLinearGroup (Fin 2) K ≃* ↥(CFSG.Open.StatedSL 2 K) :=
    (MonoidHom.ofInjective SpecialLinearGroup.toGL_injective).trans
      (MulEquiv.subgroupCongr (CFSG.Open.StatedAPI.statedSL_eq_range_toGL 2 K).symm)
  exact ((hSL.of_mulEquiv eSL).statedProj).of_mulEquiv e.symm

end CFSG.LocalAnalysis.UniquenessCase.UC22
