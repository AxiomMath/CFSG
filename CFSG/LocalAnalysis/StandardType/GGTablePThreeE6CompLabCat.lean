module

public import CFSG.LocalAnalysis.StandardType.GGTablePThreeE6LangComp
public import CFSG.LocalAnalysis.StandardType.GGExcCompSLCat
import CFSG.LocalAnalysis.StandardType.GGTablePThreeE6UniqueCompLabelCat

public section

namespace CFSG.StandardType.TablePThreeKG

open CFSG CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.AlgebraicGroups CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

section CompLabE6

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.SeitzGeneration
  CFSG.LieType.AlgebraicGroups
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Solomon.Coordinator
  CFSG.HardMathSupport.Solomon.Coordinator.LieComp
  CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple
  CFSG.StandardType.RecipeExcLang CFSG.ComponentClassification.OuterAutomorphisms

theorem compLabE6_cat_of_lang
    (d : TauCeti.ValidLieTypeIndex) (hch : d.1.characteristic = 2)
    (hd : (∃ q, d.1 = .E6 q) ∨ ∃ q, d.1 = .twistedE6 q)
    (hq : 4 ≤ CFSG.LocalAnalysis.GLTheoremA.KD264Lie.fieldSize d.1) :
    ∀ β : MulAut ((TauCeti.CFSGIndex.lie d).Group), β ∈ CFSG.ComponentClassification.OuterAutomorphisms.innAutDerived ((TauCeti.CFSGIndex.lie d).Group) →
      β ^ 3 = 1 → β ≠ 1 →
      ∀ K : Subgroup ((TauCeti.CFSGIndex.lie d).Group),
        CFSG.Open.IsComponentOf K (CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup β) →
        (∀ K' : Subgroup ((TauCeti.CFSGIndex.lie d).Group),
          CFSG.Open.IsComponentOf K' (CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup β) → K' = K) →
        ∃ lab : LargeEvenLabel, LargeEvenInLambda2 lab ∧ GGHasLabel lab (↥K ⧸ Subgroup.center ↥K) ∧
          E6CompLabel (CFSG.LocalAnalysis.GLTheoremA.KD264Lie.fieldSize d.1) lab := by
  refine uniqueCompLabelAt_e6_cat_of_lang
    (P := E6CompLabel (CFSG.LocalAnalysis.GLTheoremA.KD264Lie.fieldSize d.1))
    d hch hd hq ?_
  intro _ _ _ _ S _Fr _hFr _hΦ hq' a hT hap h1 i huniq
  obtain ⟨lab, hRL, hc⟩ := e6_lang_rationalComponents S hT hap h1 i huniq
  obtain ⟨hl, hh⟩ := hRL
  exact ⟨lab, hl, hh, hq' ▸ hc⟩

end CompLabE6

end CFSG.StandardType.TablePThreeKG

end
