module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KTab23d.Defs
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.StatementsRootModule

import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KTab23d.ReduceLine
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KTab23d.FixedLineOmega
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KTab23d.OmegaMinusLevi
import CFSG.LocalAnalysis.UniquenessCase.UC22P22d

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.KTabD

open CFSG.Open PartTwo

theorem kTab23d_omegaMinusSix {W : Type} [CommGroup W] [Finite W] (H : Subgroup (MulAut W)) (n : ℕ)
    (hnat : IsNaturalClassicalModule H n) (hperf : ⁅H, H⁆ = H) (hn : 3 ≤ n) (S : Sylow 2 ↥H)
    (h : IsOmegaMinus ↥H 6 n ∧ NatOmegaMinus H ⊤ ⊥ 6 n) :
    IsL2 (Bar2 (Hinf (pointStab H S))) (2 * n) := by
  obtain ⟨-, K, hKf, hKfin, b, c, hK, hirr, hreal⟩ := h.2
  letI := hKf
  letI := hKfin
  haveI : CharP K 2 := uc22p22d_charP_two (by omega) hK
  have hline : KTabC.SylowFixedLine (StatedOmega (StatedQuadMinus 3 K b c))
      (Pi.single (Sum.inl ⟨0, by omega⟩) 1) :=
    sylowFixedLine_omegaMinus (m := 3) (by norm_num) hirr
  obtain ⟨e1⟩ := (bar2_hinf_pointStab_equiv hreal hline S).1
  obtain ⟨e2⟩ := nonempty_bar2_hinf_lineStab_statedOmegaMinus hirr 0
  exact uc22p22d_isL2_of_omegaMinus4 (X := Bar2 (Hinf (pointStab H S))) (k := n)
    (by omega) hK b c hirr (e1.trans e2)

end CFSG.LocalAnalysis.UniquenessCase.UC22.KTabD
