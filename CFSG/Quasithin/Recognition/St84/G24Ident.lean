module

public import CFSG.Quasithin.Recognition.St84.Gen.G2qAmalGlue
public import CFSG.Quasithin.Recognition.St84.G24Vertex1Iso
public import CFSG.Quasithin.Recognition.St84.G24Vertex2Iso
public import CFSG.Quasithin.Recognition.St84.G24ModelFactsProof
public import CFSG.Quasithin.Recognition.St84.G24ModelFrames
public import CFSG.Quasithin.Recognition.St84.G24Witness
public import CFSG.Quasithin.Recognition.St84.G24DC

public section

namespace CFSG.Quasithin.F112R.St84

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.F112R

theorem g24Ident :
    ∀ (G : Type) [Group G] [Finite G] (L1 L2 S : Subgroup G), F112HypW L1 L2 S →
      VA5 L1 → VA5 L2 → G24LocalData L1 L2 S →
        IsAmalgamOfGroup (f112Amalgam L1 L2 S) (IsG2Over 2) := by
  intro G _ _ L1 L2 S hF h1 h2 hD
  have hR : Hyp111R L1 L2 S := Hyp111R.of_hyp111 rankOneListedFacts hF.1
  have hM : G24M.Facts := G24M.facts
  have hFr : G24M.FrameFacts := G24M.frameFacts
  obtain ⟨ψ₁, hψ₁S, hψ₁Q⟩ := exists_vertexIso_left hF h1 h2 hD hM hFr
  obtain ⟨ψ₂, hψ₂S, hψ₂Q⟩ := exists_vertexIso_right hF h2 hD hM hFr ψ₁ hψ₁S hψ₁Q
  have hQ := G24LocalData.pCoreOf_eq_dsQ_left hR hD.le_left
  have hQY : CFSG.Open.pCoreOf 2 G24M.M1 = G24M.Q1 := hM.pCoreOf_M1
  refine isAmalgamOfGroup_g2_of_mulEquiv_of_dcProp (f := 2) le_rfl hF.1 hD.le_left
    hD.le_right h1 h2 (G24M.natCard_F4.trans (by norm_num))
    (G24M.dcProp_g24 hM (G24M.witnesses hM)) ψ₁ ?_ hψ₁S ψ₂ ?_ hψ₂S
  · intro x
    rw [hQ, hQY]
    exact hψ₁Q x
  · intro x
    rw [hQ, hQY]
    exact hψ₂Q x

end CFSG.Quasithin.F112R.St84

end
