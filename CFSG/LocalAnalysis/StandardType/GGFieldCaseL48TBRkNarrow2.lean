module

public import CFSG.LocalAnalysis.StandardType.GGFieldCaseL48TBRkNarrow2Defs
public import CFSG.LocalAnalysis.StandardType.GGFieldCaseL48TBBridge
public import CFSG.LocalAnalysis.StandardType.GGTableBTwE6TBModel
public import CFSG.LocalAnalysis.StandardType.GGTwE6WeylTorusHolds

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly TableB

theorem largeEvenLabelAll_irredModTableB_twE6
    {p : ℕ} {lab : LargeEvenLabel} (hp : p.Prime)
    (hlab : LargeEvenInLambda2 lab) (hs : LargeEvenSplit p lab) (htag : lab.tag = .twE6)
    (h5 : 5 ≤ p) :
    LargeEvenLabelAll lab fun R _ I _ => GGIrredModTableB p R I ∨ GGWPlusTableB p R I := by
  have hdvd : p ∣ 2 ^ lab.n + 1 := by
    rcases hs with ⟨h, -⟩ | ⟨-, -, h⟩ | ⟨h | h, -⟩ | ⟨-, h⟩
    · rw [htag] at h
      exact absurd h (by simp [LargeEvenUntwisted])
    · exact h
    · rw [htag] at h
      exact absurd h (by simp)
    · rw [htag] at h
      exact absurd h (by simp)
    · omega
  exact largeEvenLabelAll_irredModTableB_of_torusIrredSCr hp
    (largeEvenLabelAll_twE6TB_irred (ggTwE6TorusIrredInput_of_model ggTwE6TorusModelInput_holds)
      hp hlab ⟨htag, hdvd, h5⟩)

theorem ggL48TableBKnownFormsRestRkOpen_of_open2
    (h : GGL48TableBKnownFormsRestRkOpen2) :
    GGL48TableBKnownFormsRestRkOpen := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h8⟩ := h
  refine ⟨h1, h2, h3, h4, h5, ?_, h8⟩
  intro p lab hp hlab hs hv hd hf ht ho
  rcases ho with ⟨htag, h5p⟩ | ho | ho
  · exact largeEvenLabelAll_irredModTableB_twE6 hp hlab hs htag h5p
  · exact h6 p lab hp hlab hs hv hd hf ht (Or.inl ho)
  · exact h6 p lab hp hlab hs hv hd hf ht (Or.inr ho)

end CFSG.StandardType
