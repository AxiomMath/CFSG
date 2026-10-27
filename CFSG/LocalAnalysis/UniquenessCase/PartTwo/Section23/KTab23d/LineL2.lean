module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KTab23d.Defs
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.StatementsRootModule

import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KTab23d.ReduceLine
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KTab23d.FixedLineSL
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KTab23d.NoInvariantLine
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KTab23d.Bar2Map
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KTab23d.Dickson
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KTab23a.Stab
import CFSG.LocalAnalysis.UniquenessCase.UC22P22d

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.KTabD

open scoped commutatorElement
open CFSG.Open

theorem kTab23d_L2 {W : Type} [CommGroup W] [Finite W] (H : Subgroup (MulAut W)) (n : ℕ)
    (hnat : IsNaturalClassicalModule H n) (hperf : ⁅H, H⁆ = H) (hn : 3 ≤ n) (S : Sylow 2 ↥H)
    (h : IsL2 ↥H n ∧ CFSG.Quasithin.BinaryNaturalSL H ⊤ ⊥ 2 n) : Hinf (pointStab H S) = ⊥ := by
  obtain ⟨hL2, K, hKf, hKfin, hKcard, hreal⟩ := h
  letI := hKf
  letI := hKfin
  haveI : CharP K 2 := uc22p22d_charP_two (by omega) hKcard
  have hline : KTabC.SylowFixedLine (StatedSL 2 K) (Pi.single 0 1) :=
    sylowFixedLine_statedSL (K := K) (d := 2) le_rfl
  obtain ⟨φ, hφ⟩ := exists_mulEquiv_pointStab_eq_map hreal hline S
  have hw₀ : (Pi.single 0 1 : Fin 2 → K) ≠ 0 := by
    intro h0
    have := congrFun h0 0
    simp at this
  have hne : pointStab H S ≠ ⊤ := by
    intro htop
    rw [hφ, map_mulEquiv_eq_top_iff] at htop
    exact lineStab_statedSL_two_ne_top hw₀ htop
  have hSP : (S : Subgroup ↥H) ≤ pointStab H S :=
    (S : Subgroup ↥H).le_normalizer.trans
      (KTabA.normalizer_le_stabilizer_fixedPointSubgroup H S)
  exact hinf_eq_bot_of_isL2_of_sylow_le (m := n) (by omega) hL2 S _ hSP hne

end CFSG.LocalAnalysis.UniquenessCase.UC22.KTabD
