module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KTab23d.Defs
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.StatementsRootModule

import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KTab23d.ReduceLine
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KTab23d.FixedLineOmega
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KTab23d.OmegaMinusLevi
import CFSG.LocalAnalysis.UniquenessCase.UC22P22d
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section18.OmegaSixMinusK
import CFSG.LocalAnalysis.AGLEmbedding.LeviBlockOrthMinusResGroup

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.KTabD

open CFSG.Open PartTwo

theorem kTab23d_omegaMinusEight {W : Type} [CommGroup W] [Finite W] (H : Subgroup (MulAut W))
    (n : ℕ) (hnat : IsNaturalClassicalModule H n) (hperf : ⁅H, H⁆ = H) (hn : 3 ≤ n)
    (S : Sylow 2 ↥H)
    (h : IsOmega8m ↥H n ∧ NatOmegaMinus H ⊤ ⊥ 8 n) :
    IsU4 (Bar2 (Hinf (pointStab H S))) n := by
  classical
  obtain ⟨-, K, hKf, hKfin, b, c, hcard, hirr, hreal⟩ := h.2
  letI : Field K := hKf
  haveI : Finite K := hKfin
  haveI : CharP K 2 :=
    CFSG.LocalAnalysis.UniquenessCase.UC22.uc22p22d_charP_two (by omega) hcard
  have hline : KTabC.SylowFixedLine (StatedOmega (StatedQuadMinus 4 K b c))
      (Pi.single (Sum.inl ⟨0, by omega⟩) 1) :=
    sylowFixedLine_omegaMinus (K := K) (m := 4) (b := b) (c := c) (by norm_num) hirr
  obtain ⟨e1⟩ := (bar2_hinf_pointStab_equiv hreal hline S).1
  obtain ⟨e2⟩ :=
    nonempty_bar2_hinf_lineStab_statedOmegaMinus (K := K) (b := b) (c := c) hirr 1
  let e3 : StatedOmega (StatedQuadMinus 3 K b c) ≃*
      StatedProj (StatedOmega (StatedQuadMinus 3 K b c)) :=
    (CFSG.AGLEmbedding.LeviBlock.orthMinusStatedProjEquiv (K := K) (b := b) (c := c)
      (n := 3) (by norm_num)).symm
  have hshape : IsOmegaMinus (Bar2 (Hinf (pointStab H S))) 6 n := by
    refine ⟨⟨3, rfl⟩, K, hKf, hKfin, b, c, hcard, hirr, ?_⟩
    exact ⟨e1.trans (e2.trans e3)⟩
  exact CFSG.LocalAnalysis.UniquenessCase.PartTwo.S18.isU4_of_isOmegaMinus hshape

end CFSG.LocalAnalysis.UniquenessCase.UC22.KTabD
