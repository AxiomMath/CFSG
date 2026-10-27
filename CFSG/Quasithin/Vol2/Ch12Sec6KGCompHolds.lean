module

public import CFSG.Quasithin.Vol2.Ch12Sec6KGCompAlt
public import CFSG.Quasithin.Vol2.Ch12Sec6KGCompOdd
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.ThreeCoverA36
public import CFSG.Quasithin.EmptyFaithful.S146zYFCCase
import CFSG.Quasithin.Vol2.Ch12Sec6KGCompPSL2
import CFSG.Quasithin.Vol2.Ch12Sec6KGCompOddHolds
import CFSG.Quasithin.Vol2.Ch12Sec6KGCompLie2BigHolds
public import CFSG.Quasithin.Vol2.Ch12Sec6KGComp

public section

namespace CFSG.Quasithin.H13.S126C

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Blueprint CFSG.Assembly.LowTwoRank

theorem factComp12626_of
    (h1 : Comp12626Alt) (h2 : Comp12626L2Odd)
    (h3 : Comp12626L3U3Odd) (h7 : Comp12626CovOdd) (h4 : Comp12626Lie2Big)
    (h5 : Comp12626Lie2Four) (h6 : Comp12626Lie2Two) (h8 : Comp12626Sporadic) :
    FactComp12626 := by
  intro Q _ K L P T v hQ h
  have := hQ.finite
  have hK := mem_cComp_top_of_isComponent h.comp
  obtain ⟨hc, -, -⟩ := Vol2Native.a36ForSQTKCat_proved Q hQ K hK
  rcases hc with ⟨-, -, hlist⟩ | ⟨-, -, hcov⟩ | hc3 | hc4
  ·
    rcases hlist with halt | ⟨p, hp, hp2, hodd⟩ | hchar2 | ⟨n, hn, hL⟩ | ⟨s, hs, hsp⟩
    · exact absurd (Or.inl halt) (h1 Q K L P T v hQ h)
    · rcases hodd with ⟨f, hf, hL2⟩ | hL3 | hU3
      · obtain ⟨rfl, rfl⟩ := h2 Q K L P T v hQ h p f hp hp2 hf hL2
        exact Or.inr (Or.inr hL2)
      · exact absurd (Or.inl hL3) (h3 Q K L P T v hQ h p hp hp2)
      · exact absurd (Or.inr hU3) (h3 Q K L P T v hQ h p hp hp2)
    · exfalso
      rcases hchar2 with ⟨f, hf⟩ | hTits
      · rcases hf with ⟨hf, hx⟩ | ⟨hf, hx⟩ | ⟨hf, hx⟩ | ⟨hf, hx⟩ | ⟨hf, hx⟩ | ⟨hf, hx⟩ |
          ⟨hfo, hf, hx⟩ | ⟨hfo, hf, hx⟩
        · obtain rfl | hf3 : f = 2 ∨ 3 ≤ f := by omega
          · exact h1 Q K L P T v hQ h (Or.inr hx)
          · exact h4 Q K L P T v hQ h f hf3 (Or.inl hx)
        · obtain rfl | rfl | hf3 : f = 1 ∨ f = 2 ∨ 3 ≤ f := by omega
          · exact h6 Q K L P T v hQ h (Or.inl hx)
          · exact h5 Q K L P T v hQ h (Or.inl hx)
          · exact h4 Q K L P T v hQ h f hf3 (Or.inr (Or.inl hx))
        · obtain rfl | hf3 : f = 2 ∨ 3 ≤ f := by omega
          · exact h5 Q K L P T v hQ h (Or.inr (Or.inl hx))
          · exact h4 Q K L P T v hQ h f hf3 (Or.inr (Or.inr (Or.inl hx)))
        · obtain rfl | hf3 : f = 2 ∨ 3 ≤ f := by omega
          · exact h5 Q K L P T v hQ h (Or.inr (Or.inr (Or.inl hx)))
          · exact h4 Q K L P T v hQ h f hf3 (Or.inr (Or.inr (Or.inr (Or.inl hx))))
        · obtain rfl | hf3 : f = 2 ∨ 3 ≤ f := by omega
          · exact h5 Q K L P T v hQ h (Or.inr (Or.inr (Or.inr (Or.inl hx))))
          · exact h4 Q K L P T v hQ h f hf3 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hx)))))
        · obtain rfl | rfl | hf3 : f = 1 ∨ f = 2 ∨ 3 ≤ f := by omega
          · exact h6 Q K L P T v hQ h (Or.inr (Or.inr (Or.inr (Or.inl hx))))
          · exact h5 Q K L P T v hQ h (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hx)))))
          · exact h4 Q K L P T v hQ h f hf3
              (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hx))))))
        · exact h4 Q K L P T v hQ h f hf
            (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨hfo, hx⟩)))))))
        · exact h4 Q K L P T v hQ h f hf
            (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨hfo, hx⟩))))))))
      · exact h6 Q K L P T v hQ h (Or.inr (Or.inr (Or.inr (Or.inr hTits))))
    · exfalso
      rcases hn with rfl | rfl
      · exact h6 Q K L P T v hQ h (Or.inr (Or.inl hL))
      · exact h6 Q K L P T v hQ h (Or.inr (Or.inr (Or.inl hL)))
    · exact absurd hsp (h8 Q K L P T v hQ h s hs)
  ·
    rcases hcov with ⟨s, p, e, hp, he, hpe, hsl⟩ | h6h | h7h | h22h
    · exfalso
      rcases hpe with ⟨rfl, hmod⟩ | ⟨hp2, rfl⟩
      · obtain rfl | rfl | he3 : e = 1 ∨ e = 2 ∨ 3 ≤ e := by omega
        · cases s
          · exact h7 Q K L P T v hQ h (Or.inr (Or.inl hsl))
          · exact absurd hmod (by decide)
        · exact h5 Q K L P T v hQ h (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨s, hsl⟩)))))
        · exact h4 Q K L P T v hQ h e he3
            (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨s, hsl⟩))))))))
      · rw [pow_one] at hsl
        exact h7 Q K L P T v hQ h (Or.inl ⟨s, p, hp, hp2, hsl⟩)
    · exact absurd (Or.inr (Or.inr h6h)) (h7 Q K L P T v hQ h)
    · exact Or.inl h7h
    · exact Or.inr (Or.inl h22h)
  · exact absurd hc3 (S146zY.not_a36Case3_of_isQuasisimple h.comp.1)
  · exact absurd hc4 (S146zY.not_a36Case4_of_isQuasisimple h.comp.1)

theorem factComp12626_of_remaining
    (h5 : Comp12626Lie2Four) (h6 : Comp12626Lie2Two) (h8 : Comp12626Sporadic) :
    FactComp12626 :=
  factComp12626_of comp12626Alt_holds comp12626L2Odd_holds comp12626L3U3Odd_holds
    comp12626CovOdd_holds comp12626Lie2Big_holds h5 h6 h8

end CFSG.Quasithin.H13.S126C
