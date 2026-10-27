module

public import CFSG.LocalAnalysis.StandardType.GGNbrTableForms
public import CFSG.LocalAnalysis.StandardType.GGTCJLabel
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R166FamA8Two
public import CFSG.Adapters.LinearFieldTransport

public section

namespace CFSG.StandardType.E6TwoSeven

open CFSG CFSG.Assembly CFSG.StandardType
open CFSG.LocalAnalysis.GLTheoremA.Y10F
open scoped MatrixGroups

theorem ggHasLabel_A21_of_mulEquiv_SL3 {X : Type} [Group X] {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 2) (e : X ≃* SL(3, K)) :
    GGHasLabel ⟨.A, 2, 1⟩ (X ⧸ Subgroup.center X) := by
  have hK2 : Nat.card K = 2 := hK
  have : Fintype K := Fintype.ofFinite K
  let φ : K ≃+* ZMod 2 := FiniteField.ringEquivOfCardEq (by
    rw [← Nat.card_eq_fintype_card, hK2, ZMod.card])
  have hSL : HasLabel (Matrix.SpecialLinearGroup (Fin 3) (ZMod 2))
      (· = (⟨.A, 2, 1⟩ : LargeEvenLabel)) :=
    hasLabel_specialLinear_zmod_two 3 (by norm_num)
  have hX : HasLabel X (· = (⟨.A, 2, 1⟩ : LargeEvenLabel)) :=
    (hasLabel_congr (e.trans (CFSG.ClassicalModels.specialLinearFieldEquiv φ (Fin 3)))
      (· = (⟨.A, 2, 1⟩ : LargeEvenLabel))).2 hSL
  exact CFSG.StandardType.TCJ.tcj_ggHasLabel_of_hasLabel hX

end CFSG.StandardType.E6TwoSeven

end
