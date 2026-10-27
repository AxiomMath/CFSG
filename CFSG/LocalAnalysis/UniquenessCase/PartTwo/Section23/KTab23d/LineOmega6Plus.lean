module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KTab23d.Defs
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.StatementsRootModule
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KTab23d.ReduceLine
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KTab23a.LinePlus
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KTab23c.SylowLine
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KTab23d.Shapes
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KTab23d.OmegaPlusStab
import CFSG.LocalAnalysis.UniquenessCase.UC22P22d

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.KTabD

open CFSG.Open PartTwo

theorem kTab23d_omegaPlusSix {W : Type} [CommGroup W] [Finite W] (H : Subgroup (MulAut W)) (n : ℕ)
    (hnat : IsNaturalClassicalModule H n) (hperf : ⁅H, H⁆ = H) (hn : 3 ≤ n) (S : Sylow 2 ↥H)
    (h : IsOmegaPlus ↥H 6 n ∧ NatOmegaPlus H ⊤ ⊥ 6 n) :
    IsL2Square (Bar2 (Hinf (pointStab H S))) n := by
  obtain ⟨-, K, hKf, hKfin, hK, hreal⟩ := h.2
  letI := hKf
  letI := hKfin
  haveI : CharP K 2 := uc22p22d_charP_two (by omega) hK
  have hK4 : 4 ≤ Nat.card K := by
    rw [hK]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) (by omega)
  haveI : Nonempty (Fin 3 ⊕ Fin 3) := ⟨Sum.inl 0⟩
  obtain ⟨U, hU, hfix⟩ :=
    KTabA.exists_fixedLine_statedOmega_plus_single (K := K) (p := 2) (m := 3) (by norm_num)
  have hline : KTabC.SylowFixedLine (StatedOmega (StatedQuadPlus 3 K))
      (Pi.single (Sum.inl ⟨0, by omega⟩) 1 : Fin 3 ⊕ Fin 3 → K) :=
    KTabC.sylowFixedLine_of_isPGroup U hU _ hfix
  obtain ⟨e1⟩ := (bar2_hinf_pointStab_equiv hreal hline S).1
  obtain ⟨e2⟩ := nonempty_bar2_hinf_lineStab_statedOmegaPlus_three (K := K) hK4
  refine ⟨Matrix.SpecialLinearGroup (Fin 2) K, Matrix.SpecialLinearGroup (Fin 2) K,
    inferInstance, inferInstance, ⟨e1.trans e2⟩, ?_, ?_⟩
  · exact isL2_of_mulEquiv_sl2 (X := Matrix.SpecialLinearGroup (Fin 2) K) (f := n)
      (by omega) hK (MulEquiv.refl _)
  · exact isL2_of_mulEquiv_sl2 (X := Matrix.SpecialLinearGroup (Fin 2) K) (f := n)
      (by omega) hK (MulEquiv.refl _)

end CFSG.LocalAnalysis.UniquenessCase.UC22.KTabD
