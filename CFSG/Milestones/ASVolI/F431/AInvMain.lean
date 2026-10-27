module

public import CFSG.Milestones.ASVolI.F431.ATop
public import CFSG.Milestones.ASVolI.F431.AInvG2
public import CFSG.Milestones.ASVolI.F431.AInvD4
public import CFSG.Milestones.ASVolI.F431.AInvF4
public import CFSG.Milestones.ASVolI.F431.AInvU4
public import CFSG.Milestones.ASVolI.F431.AInvU5
public import CFSG.Milestones.ASVolI.F431.AInvSpAll

public section

namespace CFSG.ASVolI

open CFSG.Open CFSG.ASVolI.ChF

section Main


theorem burnsideF4m_centInput : burnsideF4ja_CentInput := by
  intro κ f E _ Gp M₁ M₂ hyp hL3 hG2d hodd hor x hxG hx1 hx2 _
  cases κ
  · exact absurd rfl hL3
  · exact burnsideF4m_centInput_Sp4_all hyp hxG hx1 hx2
  · by_cases hf : 2 ≤ f
    · exact burnsideF4m_centInput_G2 hyp hf hodd hx1 hx2
    · have hf1 : 1 ≤ f := hyp.model.2.1
      obtain rfl : f = 1 := by omega
      rcases hor with h | h
      · exact absurd (burnsideF4m_top_G2two hyp) h
      · exact absurd h (by decide)
  · exact burnsideF4m_centInput_D4 hyp hodd hx1 hx2
  · by_cases hf : 3 ≤ f
    · exact burnsideF4m_centInput_F4 hyp hf hodd hx1 hx2
    · have hf1 : f = 1 := by
        obtain ⟨-, hfo, -⟩ := hyp.model
        obtain ⟨k, hk⟩ := hfo
        omega
      subst hf1
      rcases hor with h | h
      · exact absurd (burnsideF4m_top_F4two hyp) h
      · exact absurd h (by decide)
  · exact burnsideF4m_centInput_U4 hyp hodd hx1 hx2
  · exact burnsideF4m_centInput_U5 hyp hodd hx1 hx2
  · exact absurd rfl hG2d
  · rcases hor with h | h
    · exact absurd (hyp.canonical (Or.inr rfl)) h
    · exact absurd h (by decide)

end Main

end CFSG.ASVolI
