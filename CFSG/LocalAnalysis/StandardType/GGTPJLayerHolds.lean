module

public import CFSG.LocalAnalysis.StandardType.GGTPDefs
public import CFSG.LocalAnalysis.StandardType.GGTPJData
public import CFSG.LocalAnalysis.StandardType.GGTPLayerE6
public import CFSG.LocalAnalysis.StandardType.GGTPLayerTwE6
public import CFSG.LocalAnalysis.StandardType.GGReverseMarkingRaw
public import CFSG.LocalAnalysis.StandardType.GGTableBTwE6Delta
public import CFSG.Open.StatedAPI

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private theorem ggTP_hasLabel_PSL {X : Type} [Group X] {n : ℕ}
    (h : CFSG.Open.StatedClassicalModel X .PSL 6 2 n) : GGHasLabel ⟨.A, 5, n⟩ X :=
  recipeLinear_of_statedClassicalModel h

private theorem ggTP_hasLabel_PSU {X : Type} [Group X] {n : ℕ}
    (h : CFSG.Open.StatedClassicalModel X .PSU 6 2 n) : GGHasLabel ⟨.twA, 5, n⟩ X :=
  recipeUnitary_of_statedClassicalModel h

theorem ggTPJLayerInput_holds
    : GGTPJLayerInput := by
  intro lab hdep hΛ
  rcases hdep with ⟨htag, h3⟩ | ⟨htag, h3⟩
  ·
    obtain ⟨t, l, n⟩ := lab
    dsimp only at htag h3
    subst htag
    intro Q hQ
    obtain ⟨K, _, _, hK, hQ⟩ := hQ
    refine ⟨K, inferInstance, inferInstance, hK, hQ, ?_⟩
    intro _ _ L' _ _ ψ A hTB hA hZ c hc J hJ
    obtain ⟨ER, X, _, hER, ⟨e⟩, hX, hmodel⟩ :=
      ggTPLayerModel_E6 hΛ.1 hK h3 ψ A hTB hA hc
    have h3X := ggTP_three_dvd_card_PSL6 hΛ.1 h3 hmodel
    have hc' : ∃ φ : MulAut _, ∀ l', φ (ψ l') = ψ ((c : MulAut L') l') := by
      obtain ⟨φ, -, hφ⟩ := hTB.2.2.2.2.1 c c.2
      exact ⟨φ, hφ⟩
    obtain ⟨⟨e'⟩, hZJ, h3J⟩ := ggTPJData_of_layer ψ hTB.1 hTB.2.1 hZ hc' hER e hX h3X hJ
    refine ⟨?_, hZJ, h3J⟩
    exact ggTP_hasLabel_PSL (CFSG.Open.StatedAPI.statedClassicalModel_of_mulEquiv e'.symm hmodel)
  ·
    refine TwE6Delta.labelAll (lab := lab) htag
      (Q := fun R _ I => IsSimpleGroup R → (∃ a b : R, a * b ≠ b * a) → GGTPJLayer lab R I) ?_
    intro K _ _ hK _ _ L' _ _ ψ A hTB hA hZ c hc J hJ
    obtain ⟨ER, X, _, hER, ⟨e⟩, hX, hmodel⟩ :=
      ggTPLayerModel_TwE6 hΛ.1 h3 hK ψ A hTB hA hc
    have h3X := ggTP_three_dvd_card_PSU6 hΛ.1 h3 hmodel
    have hc' : ∃ φ : MulAut _, ∀ l', φ (ψ l') = ψ ((c : MulAut L') l') := by
      obtain ⟨φ, -, hφ⟩ := hTB.2.2.2.2.1 c c.2
      exact ⟨φ, hφ⟩
    obtain ⟨⟨e'⟩, hZJ, h3J⟩ := ggTPJData_of_layer ψ hTB.1 hTB.2.1 hZ hc' hER e hX h3X hJ
    refine ⟨?_, hZJ, h3J⟩
    have : ggTPJLabel lab = ⟨.twA, 5, lab.n⟩ := by
      simp [ggTPJLabel, htag]
    rw [this]
    exact ggTP_hasLabel_PSU (CFSG.Open.StatedAPI.statedClassicalModel_of_mulEquiv e'.symm hmodel)

end CFSG.StandardType

end
