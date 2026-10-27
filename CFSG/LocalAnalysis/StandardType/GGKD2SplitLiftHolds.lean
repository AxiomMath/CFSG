module

public import CFSG.LocalAnalysis.StandardType.GGKD2UnitaryPieces1615
public import CFSG.LocalAnalysis.StandardType.GGKD2UnitaryNotThreeDvd
public import CFSG.LocalAnalysis.StandardType.GGKD2LinearHolds1615

public section

namespace CFSG.StandardType.KD2Pieces1615

open CFSG CFSG.Assembly CFSG.StandardType S2MathAs3_1615

theorem corner1584_split_lift_of_pieces (hU3 : SplitLiftUnitaryThreeDvd)
    (hU4 : SplitLiftUnitaryNotThreeDvd) : corner1584_split_lift := by
  have hL := splitLiftLinear_holds
  intro lab hlab
  by_cases hc : ClassicalLab lab
  · rcases hc with htag | htag
    · refine LargeEvenLabelAll.mono (fun R _ I _ h => ?_) (hL lab hlab htag)
      intro L' _ _ ψ hψ hker hperf e J a hsetup _ hsplit
      exact h L' ψ hψ hker hperf e J a hsetup hsplit
    · by_cases hdvd : 3 ∣ 2 ^ lab.n + 1
      · refine LargeEvenLabelAll.mono (fun R _ I _ h => ?_) (hU3 lab hlab htag hdvd)
        intro L' _ _ ψ hψ hker hperf e J a hsetup _ hsplit
        exact h L' ψ hψ hker hperf e J a hsetup hsplit
      · refine LargeEvenLabelAll.mono (fun R _ I _ h => ?_) (hU4 lab hlab htag hdvd)
        intro L' _ _ ψ hψ hker hperf e J a hsetup _ hsplit
        exact h L' ψ hψ hker hperf e J a hsetup hsplit
  · intro Q hQ
    exact largeEvenRawDatum_mono
      (fun R _ I F hq => ⟨hq, fun L' _ _ ψ hψ hker hperf e J a hsetup hcl _ => absurd hcl hc⟩) hQ

end CFSG.StandardType.KD2Pieces1615

end
