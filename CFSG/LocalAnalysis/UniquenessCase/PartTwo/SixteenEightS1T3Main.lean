module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightS1T3EngineShape
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightS1T3SpecialShape
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightS1T3SmallRowsD
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightS1T3SmallRowsE

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G] {D : Data G} {V₀ V L : Subgroup G}
  {hV : IsElemAbelian 2 V}

theorem S16gRowCtx.false_of_sum_three_nat (h : S16gRowCtx D V₀ V L hV)
    (hGA : CFSG.Open.GriessAllModelsStatement)
    (hSchur : CFSG.ComponentClassification.SolAltLit.SchurAlternatingMultiplierInput)
    (hsum : SumOfNatShape (lBar V₀ V hV L) (commSub ⊤ (lBar V₀ V hV L))
      (commSub ⊤ (lBar V₀ V hV L) ⊓ fixV (lBar V₀ V hV L)) 3)
    (htrans : ∀ I₁ ∈ irrSet (lBar V₀ V hV L), ∀ I₂ ∈ irrSet (lBar V₀ V hV L),
      ∃ g ∈ Mbar D.M V₀ V hV ⊓ Subgroup.normalizer
        (lBar V₀ V hV L : Set (MulAut (Vtil V₀ V hV))), I₂ = I₁.map g.toMonoidHom) :
    False := by
  have hT := h.threeNat hsum htrans
  by_cases h3 : 3 ∈ D.sig
  · rcases hT.shape_cases with hE | hS
    · exact h.false_of_engine_shape hGA hSchur hT h3 hE
    · exact h.false_of_special_shape hGA hSchur hsum hT h3 hS
  · by_cases h7 : 7 ∈ D.sig ∧ (IsSLn ↥(lBar V₀ V hV L) 6 1 ∨ IsSLn ↥(lBar V₀ V hV L) 7 1)
    · exact h.false_of_seven_mem_sig_sl hGA hSchur hT h3 h7.1 h7.2
    · exact h.false_of_not_three_mem_sig hGA hSchur hsum hT h3 (not_and_or.mp h7)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
