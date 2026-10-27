module

public import CFSG.LocalAnalysis.StandardType.GGKD2Connected1619ClassicalGlue
public import CFSG.LocalAnalysis.StandardType.GGKD2Connected1619OrthCenter
public import CFSG.LocalAnalysis.StandardType.GGKD2Connected1619OrthProducer
public import CFSG.LocalAnalysis.StandardType.GGKD2Connected1619OrthTransport
public import CFSG.LocalAnalysis.StandardType.GGKD2Connected1619OrthDerived

public section

namespace S2MathAs3_1619Final

open CFSG CFSG.Assembly CFSG.StandardType CFSG.Open S2MathAs3_1615

theorem orthModelAction_holds {K : Type} [Field K] [Finite K] [CharP K 2] {n : ℕ} (hn : 8 ≤ n)
    (Phi : QuadraticForm K (Fin n → K)) (hnd : (QuadraticMap.polarBilin Phi).Nondegenerate) :
    ClassicalModelAction ↥(StatedOmega ⇑Phi) := by
  refine classicalModelAction_of_mulEquiv
    (CFSG.StandardType.TableBOrth.omegaEquivOrthDerived Phi) ?_
  refine orthDerivedModelAction_holds hnd ?_
  simpa using hn

theorem actionTag_orth_high :
    ∀ lab : LargeEvenLabel, (lab.tag = .D ∨ lab.tag = .twD) → 4 ≤ lab.rank →
      LargeEvenInLambda2 lab → LargeEvenLabelAll lab (fun R _ I _ => RawActionAt R I) := by
  have hP := orthProducer_holds
  intro lab htag hr hlab
  refine LargeEvenLabelAll.mono (fun R _ I _ h => ?_) (hP lab hlab htag hr)
  obtain ⟨K, fK, finK, chK, hcard, Phi, hnd, θ, hθ⟩ := h
  have hn : 8 ≤ 2 * lab.rank := by omega
  exact rawActionAt_of_model θ hθ (orthModelAction_holds hn Phi hnd) (orthCenter_trivial hn Phi hnd)

end S2MathAs3_1619Final

end
