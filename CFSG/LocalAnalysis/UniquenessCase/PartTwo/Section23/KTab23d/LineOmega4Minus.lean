module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KTab23d.Defs
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.StatementsRootModule

import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KTab23d.ReduceLine
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KTab23d.NoInvariantLine
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KTab23d.Bar2Map
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KTab23d.Dickson
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KTab23a.Stab
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KTab23c.SylowLine
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section18.EighteenThirteen

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.KTabD

open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.Open
open scoped commutatorElement

theorem kTab23d_omegaMinusFour {W : Type} [CommGroup W] [Finite W] (H : Subgroup (MulAut W))
    (n : ℕ) (hnat : IsNaturalClassicalModule H n) (hperf : ⁅H, H⁆ = H) (hn : 3 ≤ n)
    (S : Sylow 2 ↥H) (h : IsOmegaMinus ↥H 4 n ∧ NatOmegaMinus H ⊤ ⊥ 4 n) :
    Hinf (pointStab H S) = ⊥ := by
  obtain ⟨hOm, -, K, hKf, hKfin, b, c, hKcard, hirr, hreal⟩ := h
  letI := hKf
  letI := hKfin
  haveI : CharP K 2 := uc22p22d_charP_two (by omega) hKcard
  have hL2 : IsL2 ↥H (2 * n) := S18.isL2_of_isOmegaMinus_four (by omega) hOm
  have hline := KTabC.sylowFixedLine_minus K b c hirr
  obtain ⟨φ, hφ⟩ := exists_mulEquiv_pointStab_eq_map hreal hline S
  have hne : pointStab H S ≠ ⊤ := by
    intro htop
    rw [hφ, map_mulEquiv_eq_top_iff] at htop
    exact lineStab_statedOmegaMinus_two_ne_top hirr htop
  have hSP : (S : Subgroup ↥H) ≤ pointStab H S :=
    (S : Subgroup ↥H).le_normalizer.trans
      (KTabA.normalizer_le_stabilizer_fixedPointSubgroup H S)
  exact hinf_eq_bot_of_isL2_of_sylow_le (m := 2 * n) (by omega) hL2 S _ hSP hne

end CFSG.LocalAnalysis.UniquenessCase.UC22.KTabD
