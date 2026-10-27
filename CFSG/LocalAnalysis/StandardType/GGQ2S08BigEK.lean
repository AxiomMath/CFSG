module

public import CFSG.LocalAnalysis.StandardType.GGQ2S08BigRange
public import CFSG.LocalAnalysis.StandardType.GGQ2S08ReflEK
public import CFSG.LocalAnalysis.StandardType.GGQ2S08SmallCells

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

theorem ggQ2s08_ek_of_small_big
    (hSmall : GGQ2ReflEKSmallInput) (hA : GGQ2S08BigShapeAInput)
    (hT : GGQ2TableBI1Fail) (hKG : GGReflClassLargeThree)
    (hTBW : GGTBWNormInputOn (fun p lab => p = 3 ∧ GGQ2S08BigLabel lab))
    (hCen : GGQ2S08BigCenterInput) (hOut : GGQ2S08BigInnerPartInput) (hRig : GGLabelRigidInput)
    (hLB : GGLBalanceInput) (hP : GGStdSubPrimeInput) (hΓi : GGQ2GammaXOffI1Input)
    (hTBN : GGQ2TableBNbr) (hLNC : GGLNoncyclicInput) : GGQ2ReflEKOffI1Input := by
  obtain ⟨hSE, hSK⟩ := hSmall
  have hBig : ∀ {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G},
      GGQTwoSetting 3 B Bs x L D J → ¬ GGQTwoI1 Bs D J →
      4 ∣ Nat.card ↥(ggAutomizer J Bs) → 3 ^ 9 < Nat.card ↥Bs →
      ∀ (g : G) (φ : MulAut ↥Bs), GGQ2Ind Bs g φ → GGIsReflection 3 φ →
        g ∈ Subgroup.normalizer (ggG0 3 B x L D J : Set G) := by
    intro G _ _ B Bs x L D J hS hI1 hCav h9 g φ hInd hR
    exact ggQ2s08_bigRange_of_shapeA hA hT hKG hTBW hCen hOut hRig hLB hP hΓi hTBN hS hI1 hCav
      (hLNC G 3 B x L hS.1.1.1) h9 g φ hInd hR
  refine ⟨?_, ?_⟩
  · intro G _ _ p B Bs x L D J hS hp hI1 hCav g φ hInd hR hM hC hE
    subst hp
    by_cases h : Nat.card ↥Bs ≤ 3 ^ 9
    · exact hSE hS rfl hI1 hCav h g φ hInd hR hM hC hE
    · exact hBig hS hI1 hCav (not_le.mp h) g φ hInd hR
  · intro G _ _ p B Bs x L D J hS hp hI1 hCav g φ hInd hR hM hC hE y K hN hfix hK1 hK2
    subst hp
    by_cases h : Nat.card ↥Bs ≤ 3 ^ 9
    · exact hSK hS rfl hI1 hCav h g φ hInd hR hM hC hE y K hN hfix hK1 hK2
    · exact hBig hS hI1 hCav (not_le.mp h) g φ hInd hR

end CFSG.StandardType

end
