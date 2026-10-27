module

public import CFSG.LocalAnalysis.StandardType.GGKD2Connected1619ClassicalGlue
public import CFSG.LocalAnalysis.StandardType.GGKD2Connected1619ComponentFactor
public import CFSG.LocalAnalysis.StandardType.GGKD2Connected1619SpCenter
public import CFSG.LocalAnalysis.StandardType.GGKD2Connected1619SpProducer
public import CFSG.LocalAnalysis.StandardType.GGKD2Connected1619SpFixed
public import CFSG.LocalAnalysis.StandardType.GGKD2Connected1619SpPaired
public import CFSG.LocalAnalysis.StandardType.GGKD2Connected1619SpUnitary

public section

namespace S2MathAs3_1619Final

open CFSG CFSG.Assembly CFSG.StandardType CFSG.Open S2MathAs3_1615
open CFSG.LocalAnalysis.GLTheoremA.K1419

theorem spModelAction_holds {m : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2] :
    ClassicalModelAction ↥(StatedSp m K) := by
  intro x hx1 hx3 C hC hlab y hxy hyC
  obtain ⟨n, hn1, hK⟩ : ∃ n : ℕ, 1 ≤ n ∧ Nat.card K = 2 ^ n := by
    letI : Fintype K := Fintype.ofFinite K
    obtain ⟨n, -, hn⟩ := FiniteField.card K 2
    refine ⟨(n : ℕ), n.pos, ?_⟩
    rw [Nat.card_eq_fintype_card, hn]
  have hm : 1 ≤ m := by
    by_contra h
    have hm0 : m = 0 := by omega
    subst hm0
    exact hx1 (Subsingleton.elim _ _)
  obtain ⟨A₁, A₂, hcomm, hY, hxA, ⟨s, ⟨e₁⟩⟩, hA₂⟩ := k1419ClsSympCent hK hn1 hm x hx3 hx1
  rcases component_le_factor hcomm hY hC with hle | hle
  · exact spFixedBlock_action hcomm hY e₁ hC hle hlab hxy hyC
  · rcases hA₂ with ⟨r, hr, ⟨e₂⟩⟩ | ⟨r, E, fE, finE, τ, hτ, hr, hE, hτF, ⟨e₂⟩⟩
    · exact (spPairedBlock_false hx1 hx3 hxA (hY ▸ le_sup_right) hr e₂ hC hle hlab).elim
    · exact spUnitaryBlock_action hcomm hY hxA hr hE hτF e₂ hC hle hlab hxy hyC

theorem actionTag_B_holds : ActionTag .B := by
  have hP := spProducer_holds
  intro lab htag hlab
  refine LargeEvenLabelAll.mono (fun R _ I _ h => ?_) (hP lab hlab (Or.inl htag))
  obtain ⟨K, fK, finK, chK, hcard, θ, hθ⟩ := h
  exact rawActionAt_of_model θ hθ spModelAction_holds spCenter_trivial

theorem actionTag_C_holds : ActionTag .C := by
  have hP := spProducer_holds
  intro lab htag hlab
  refine LargeEvenLabelAll.mono (fun R _ I _ h => ?_) (hP lab hlab (Or.inr htag))
  obtain ⟨K, fK, finK, chK, hcard, θ, hθ⟩ := h
  exact rawActionAt_of_model θ hθ spModelAction_holds spCenter_trivial

end S2MathAs3_1619Final

end
