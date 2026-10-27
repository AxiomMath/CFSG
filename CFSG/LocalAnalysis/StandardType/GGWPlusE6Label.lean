module

public import CFSG.LocalAnalysis.StandardType.GGWPlusE6
public import CFSG.LocalAnalysis.StandardType.GGWPlusNarrow3Defs
public import CFSG.LocalAnalysis.StandardType.GGTableBExcE6ThreeLabel

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly TableB CFSG.LieType.Chevalley CFSG.Blueprint.Chevalley

theorem largeEvenLabelAll_wplus_E6_three
    {lab : LargeEvenLabel} (hlab : LargeEvenInLambda2 lab) (h : GGL48IrredOpenLabel3 3 lab) :
    LargeEvenLabelAll lab fun R _ I _ => GGWPlusTableB 3 R I := by
  obtain ⟨t, l, n⟩ := lab
  obtain ⟨ht, -, h3⟩ := h
  dsimp only at ht
  subst ht
  intro Q hQ
  change LargeEvenRecipeChevalley (LargeEvenCartanE 6) (2 ^ n) false Q at hQ
  obtain ⟨K, _, _, hK, hQ'⟩ := hQ
  change LargeEvenRecipeChevalley (LargeEvenCartanE 6) (2 ^ n) false
    fun R _ I F => Q R I F ∧ GGWPlusTableB 3 R I
  refine ⟨K, inferInstance, inferInstance, hK, hQ', ?_⟩
  exact ggWPlusTableB_E6_three n hlab.1 hK h3

end CFSG.StandardType
