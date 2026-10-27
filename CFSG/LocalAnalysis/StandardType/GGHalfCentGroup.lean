module

public import CFSG.Assembly.LargeEvenDefs
public import CFSG.LocalAnalysis.ComponentInitial.CommutingBlock
public import CFSG.LocalAnalysis.StandardType.GGSixStepTwoCoordModelSLCompParts

public section

namespace CFSG.StandardType.GGHalf

open CFSG.Assembly

theorem eq_of_isComponentOf_isQuasisimple {G : Type*} [Group G] {J A : Subgroup G}
    (hJ : CFSG.Assembly.IsQuasisimple J) (hA : IsComponentOf A J) : A = J := by
  have hJ' : CFSG.IsQuasisimple J :=
    (CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native J).1 hJ
  have h := CoordSL.eq_of_isComponentOf_range hJ' J.subtype (L₁ := A)
    (by rwa [Subgroup.range_subtype])
  rwa [Subgroup.range_subtype] at h

theorem ne_bot_of_isComponentOf {G : Type*} [Group G] {H Z : Subgroup G}
    (hZ : IsComponentOf Z H) : Z ≠ ⊥ := by
  intro h
  refine LinSemisimple.false_of_isQuasisimple_of_commute hZ.2.2 fun x hx y hy => ?_
  rw [h, Subgroup.mem_bot] at hx hy
  rw [hx, hy]

theorem layer_ne_component_of_two_components {G : Type*} [Group G]
    {H A B : Subgroup G} (hA : IsComponentOf A H) (hB : IsComponentOf B H) (hAB : A ≠ B) :
    ¬ ∃ J : Subgroup G, J = LargeEvenLayer H ∧ IsComponentOf J H := by
  rintro ⟨J, hJ, hJc⟩
  have hle : ∀ {K : Subgroup G}, IsComponentOf K H → K ≤ J := fun {K} hK => by
    rw [hJ]
    exact le_sSup (s := {K : Subgroup G | IsComponentOf K H}) hK
  have hAJ : A = J :=
    eq_of_isComponentOf_isQuasisimple hJc.2.2
      (CFSG.LocalAnalysis.ComponentInitial.isComponentOf_of_le hA (hle hA) hJc.1)
  have hBJ : B = J :=
    eq_of_isComponentOf_isQuasisimple hJc.2.2
      (CFSG.LocalAnalysis.ComponentInitial.isComponentOf_of_le hB (hle hB) hJc.1)
  exact hAB (hAJ.trans hBJ.symm)

end CFSG.StandardType.GGHalf

end
