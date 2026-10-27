module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KTab23d.Defs
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.StatementsRootModule
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KTab23d.ReduceLine
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KTab23a.LineSU
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KTab23c.SylowLine
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KTab23d.Shapes
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KTab23d.UnitaryLevi
import CFSG.ClassicalGroups.UnitaryFlag.StatedBridge

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.KTabD

open CFSG.Open PartTwo
open CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag

theorem kTab23d_su4 {W : Type} [CommGroup W] [Finite W] (H : Subgroup (MulAut W)) (n : ℕ)
    (hnat : IsNaturalClassicalModule H n) (hperf : ⁅H, H⁆ = H) (hn : 3 ≤ n) (S : Sylow 2 ↥H)
    (h : ∃ a : ℕ, n = 2 * a ∧ IsSUn ↥H 4 a ∧ NatSUn H ⊤ ⊥ 4 a) :
    ∃ a : ℕ, n = 2 * a ∧ IsL2 (Bar2 (Hinf (pointStab H S))) a := by
  obtain ⟨a, hna, -, hsu⟩ := h
  obtain ⟨K, hKfield, hKfin, hKcard, hreal⟩ := hsu
  letI := hKfield
  letI := hKfin
  have ha : 2 ≤ a := by omega
  have hdata : UnitaryFieldData 2 a K := unitaryFieldDataOfCard hKcard
  haveI : CharP K 2 := hdata.charP
  obtain ⟨U, hU, hfix⟩ :=
    KTabA.exists_fixedLine_statedSU_suLine (K := K) (r := 2 ^ a) (d := 4) hKcard (by norm_num)
  have hline : KTabC.SylowFixedLine (StatedSU 4 (2 ^ a) K)
      (Pi.single 0 1 + Pi.single 1 1 : Fin 4 → K) :=
    KTabC.sylowFixedLine_of_isPGroup U hU _ hfix
  obtain ⟨e1⟩ := (bar2_hinf_pointStab_equiv hreal hline S).1
  obtain ⟨e2⟩ := nonempty_bar2_hinf_lineStab_statedSU_four hdata ha
  exact ⟨a, hna,
    isL2_of_mulEquiv_sl2 (K := hdata.fixedField) (f := a) ha hdata.card_fixedField (e1.trans e2)⟩

end CFSG.LocalAnalysis.UniquenessCase.UC22.KTabD
