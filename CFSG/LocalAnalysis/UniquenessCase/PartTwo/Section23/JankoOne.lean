module

public import CFSG.LocalAnalysis.QuasithinUnique.K1.SporadicJ1Model
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.UniquenessCase.UC22Defs
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels
public import CFSG.Walter.Models

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

theorem kJ1_holds :
    ∀ (X : Type) [Group X] [Finite X], IsJ1 X →
      Nat.card X = 175560 ∧ IsSimpleGroup X ∧ ∀ θ : MulAut X, ∃ x : X, θ = MulAut.conj x := by
  intro X _ _ hX
  obtain ⟨e⟩ := hX
  let f : X ≃* CFSG.Open.walterJ1 := e.trans CFSG.Walter.walterJ1EquivNative.symm
  refine ⟨?_, ?_, fun θ => ?_⟩
  · rw [Nat.card_congr f.toEquiv]
    exact CFSG.Walter.J1Props.card_walterJ1
  · haveI : IsSimpleGroup CFSG.Open.walterJ1 := CFSG.Walter.J1Props.J1_simple
    exact f.isSimpleGroup
  · obtain ⟨x, hx⟩ := CFSG.QuasithinUnique.K1.autInner_of_mulEquiv f
      CFSG.QuasithinUnique.K1.autInner_walterJ1 θ
    refine ⟨x⁻¹, MulEquiv.ext fun y => ?_⟩
    rw [hx y, MulAut.conj_apply, inv_inv]

end CFSG.LocalAnalysis.UniquenessCase.UC22

end
