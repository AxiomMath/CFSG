module

public import CFSG.Quasithin.Vol2.Ch12Sec6KGComp
public import CFSG.Quasithin.Vol2.Ch12Sec6KGCompLie2BigSp4
public import CFSG.Quasithin.Vol2.Ch12Sec6KGCompLie2BigCov

public section

namespace CFSG.Quasithin.H13.S126C

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Blueprint CFSG.Assembly.LowTwoRank

@[expose] def Comp12626Lie2BigExc : Prop :=
  ∀ (Q : Type) [Group Q] (K L P T : Subgroup Q) (v : Q), Vol2Native.SQTKHypCat Q →
    Conf12626 K L P T v → ∀ f : ℕ, 3 ≤ f →
      ¬ (ChevalleyExceptionalModel ↥K .G2 2 f ∨ ChevalleyExceptionalModel ↥K .trialityD4 2 f ∨
        (Odd f ∧ ReeTitsModel ↥K .twistedF4 2 f) ∨ (Odd f ∧ SuzukiModel ↥K 2 f))

theorem comp12626Lie2Big_of (hE : Comp12626Lie2BigExc) : Comp12626Lie2Big := by
  intro Q _ K L P T v hQ h f hf hK
  have := hQ.finite
  have hA := h.autConf
  rcases hK with hK | hK | hK | hK | hK | hK | hK | hK | ⟨s, hK⟩
  · exact false_of_autConf_psl2 hf hK hA
  · exact false_of_autConf_psl3 hf hK hA
  · exact false_of_autConf_psu3 hf hK hA
  · exact false_of_autConf_psp4 hf hK hA
  · exact hE Q K L P T v hQ h f hf (Or.inl hK)
  · exact hE Q K L P T v hQ h f hf (Or.inr (Or.inl hK))
  · exact hE Q K L P T v hQ h f hf (Or.inr (Or.inr (Or.inl hK)))
  · exact hE Q K L P T v hQ h f hf (Or.inr (Or.inr (Or.inr hK)))
  · exact false_of_autConf_slEps3 hf hK hA

end CFSG.Quasithin.H13.S126C
