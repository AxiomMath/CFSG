module

public import CFSG.LocalAnalysis.StandardType.GGKD2Leaf6Linear
public import CFSG.LocalAnalysis.StandardType.GGKD2Leaf6Unitary

public section

namespace CFSG.StandardType.KD2Pieces1615

open CFSG CFSG.Assembly CFSG.StandardType S2MathAs3_1615

theorem corner1584_nonsplit_shape_holds : corner1584_nonsplit_shape := by
  intro lab hlab Q hQ
  by_cases hA : lab.tag = .A
  · unfold CFSG.StandardType.LargeEvenRawDatum at hQ ⊢
    simp only [hA] at hQ ⊢
    obtain ⟨K, fK, finK, hK, hq⟩ := hQ
    refine ⟨K, fK, finK, hK, hq, ?_⟩
    intro L' _ _ ψ hψ hker hperf e J a hset _ hnot
    exact (leaf6Linear_false hlab hA hK ψ hψ hker hperf hset hnot).elim
  · by_cases hU : lab.tag = .twA
    · unfold CFSG.StandardType.LargeEvenRawDatum at hQ ⊢
      simp only [hU] at hQ ⊢
      obtain ⟨K, fK, finK, hK, hq⟩ := hQ
      refine ⟨K, fK, finK, hK, hq, ?_⟩
      intro L' _ _ ψ hψ hker hperf e J a hset _ hnot
      exact leaf6Unitary_shape hlab hU hK ψ hψ hker hperf hset hnot
    · refine largeEvenRawDatum_mono (fun R _ I F hq => ⟨hq, ?_⟩) hQ
      intro L' _ _ ψ hψ hker hperf e J a hset hclass
      exact (hclass.elim hA hU).elim

end CFSG.StandardType.KD2Pieces1615

end
