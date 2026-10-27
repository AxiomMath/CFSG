module

public import CFSG.LocalAnalysis.StandardType.GGTBJNoB2derExcBig
public import CFSG.LocalAnalysis.StandardType.GGTBJNoB2derExcSmall
public import CFSG.LocalAnalysis.StandardType.GGTBJNoB2derExcField
public import CFSG.LocalAnalysis.StandardType.GGTBJNoB2derExcTits

public section

namespace CFSG.StandardType.S2MathAs4B2der1822

open CFSG CFSG.Assembly

theorem exceptionalNoB2derInput_holds : ExceptionalNoB2derInput := by
  intro lab hΛ hE
  have hbig := noB2derInput_exceptionalBig lab hΛ
  have htw := noB2derInput_twB2 lab hΛ
  have htri := noB2derInput_triD4_two lab hΛ
  have hfield := noB2derInput_fieldFour lab hΛ
  have hn : 1 ≤ lab.n := hΛ.1
  obtain ⟨tag, rank, n⟩ := lab
  cases tag <;> simp only [ExceptionalLab] at hE
  · exact hbig (Or.inr (Or.inl rfl))
  · exact hbig (Or.inr (Or.inr (Or.inl rfl)))
  · exact hbig (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  · exact hbig (Or.inl rfl)
  · exact hbig (Or.inr (Or.inr (Or.inr (Or.inr rfl))))
  · have hn' : 1 ≤ n := hn
    rcases Nat.lt_or_ge n 2 with h | h
    · exact htri ⟨rfl, show n = 1 by omega⟩
    · exact hfield (Or.inr (Or.inl ⟨rfl, h⟩))
  · exact hfield (Or.inl rfl)
  · exact htw rfl
  · exact hfield (Or.inr (Or.inr rfl))

theorem smallDerivedNoB2derInput_holds : SmallDerivedNoB2derInput := by
  intro lab hΛ hS
  have hb := noB2derInput_B2der lab hΛ
  have hg := noB2derInput_G2der lab hΛ
  have ht := noB2derInput_twF4der lab hΛ
  obtain ⟨tag, rank, n⟩ := lab
  cases tag <;> simp only [SmallDerivedLab] at hS
  · exact hb rfl
  · exact hg rfl
  · exact ht rfl

end CFSG.StandardType.S2MathAs4B2der1822

end
