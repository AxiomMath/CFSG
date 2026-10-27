module

public import CFSG.Quasithin.Vol2.Ch6Sec2Lem8Res

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Quasithin

theorem hasE22LieQuot_of_isCharTwoBigE22 {Γ : Type} [Group Γ] {H M K : Subgroup Γ}
    (hKH : K ≤ H) (h : IsCharTwoBigE22 H M K) : E2.HasE22LieQuot K := by
  rcases h with ⟨m, hm, hL | hS⟩ | ⟨m, hm, hU | hL3 | hSp⟩
  · exact E2.hasE22LieQuot_of_star hKH (by omega) (Or.inl ⟨by omega, Or.inl hL⟩)
  · exact E2.hasE22LieQuot_of_star hKH (by omega) (Or.inl ⟨by omega, Or.inr (Or.inl hS)⟩)
  · exact E2.hasE22LieQuot_of_star hKH hm (Or.inl ⟨hm, Or.inr (Or.inr hU)⟩)
  · exact E2.hasE22LieQuot_of_star hKH hm (Or.inr (Or.inl hL3))
  · have hm1 : m ≠ 1 := by omega
    simp only [E2.IsSp4Prime, hm1, ↓reduceIte] at hSp
    exact E2.hasE22LieQuot_of_star hKH hm (Or.inr (Or.inr hSp))

theorem res628Lie_holds : Res628Lie := by
  intro G _ _ T M L V hyp _ H hH _ K hK hbig
  exact hyp.noLie H hH K hK (hasE22LieQuot_of_isCharTwoBigE22 (le_of_mem_cComp hK) hbig)

end CFSG.Quasithin.H13
