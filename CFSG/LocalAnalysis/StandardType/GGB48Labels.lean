module

public import CFSG.LocalAnalysis.StandardType.GGTypeANbrLabels

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Open

theorem statedClassicalModel_of_hasLabel_C32 {X : Type} [Group X]
    (hX : GGHasLabel ⟨.C, 3, 2⟩ X) : StatedClassicalModel X .PSp 3 2 2 := by
  obtain ⟨K, hF, hfin, hK, ⟨e⟩⟩ := hX
  exact ⟨by simp only [StatedLieAdmissible]; norm_num, K, hF, hfin, hK, ⟨e⟩⟩

theorem statedClassicalModel_of_hasLabel_D32 {X : Type} [Group X]
    (hX : GGHasLabel ⟨.D, 3, 2⟩ X) : StatedClassicalModel X .PSL 4 2 2 := by
  have hΛ : LargeEvenInLambda2 ⟨.A, 3, 2⟩ := by norm_num [LargeEvenInLambda2]
  exact statedClassicalModel_of_hasLabel_typeA hΛ (ggHasLabel_D3_iff_A3.mp hX)

end CFSG.StandardType

end
