module

public import CFSG.Quasithin.Vol2.Ch12Sec6KGCompOdd
public import CFSG.Quasithin.Vol2.Ch12Sec6KGCompAlt
import CFSG.LocalAnalysis.ComponentClassification.SymmetricLocalLinearFourTwo
import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A134Families
public import CFSG.Quasithin.Vol2.Ch12Sec6KGComp

public section

namespace CFSG.Quasithin.H13.S126C

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Blueprint CFSG.Assembly.LowTwoRank

@[expose] def Comp12626Lie2TwoRest : Prop :=
  ∀ (Q : Type) [Group Q] (K L P T : Subgroup Q) (v : Q), Vol2Native.SQTKHypCat Q →
    Conf12626 K L P T v →
      ¬ (StatedClassicalModel ↥K .PSL 5 2 1 ∨ ChevalleyExceptionalModel ↥K .trialityD4 2 1 ∨
        ReeTitsModel ↥K .Tits 2 1)

variable {Q : Type} [Group Q] {K L P T : Subgroup Q} {v : Q}

theorem not_psl32_of_l2Odd (h2 : Comp12626L2Odd) (hQ : Vol2Native.SQTKHypCat Q)
    (h : Conf12626 K L P T v) : ¬ StatedClassicalModel ↥K .PSL 3 2 1 := fun hK => by
  have h7 := Vol2Native.statedClassicalModel_psl_two_seven_of_three_two hK
  have := (h2 Q K L P T v hQ h 7 1 (by norm_num) (by norm_num) (Or.inl rfl) h7).1
  omega

theorem not_psl42 (hQ : Vol2Native.SQTKHypCat Q)
    (h : Conf12626 K L P T v) : ¬ StatedClassicalModel ↥K .PSL 4 2 1 := fun hK => by
  have hL : LieModel ↥K .PSL 4 2 1 := Or.inl ⟨by decide, hK⟩
  obtain ⟨e⟩ := (CFSG.ComponentClassification.SymmetricLocal.lie_model_linear_four_two_iff ↥K).mp hL
  exact comp12626Alt_holds Q K L P T v hQ h (Or.inl ⟨8, by norm_num, le_rfl, ⟨e⟩⟩)

theorem comp12626Lie2Two_of (h2 : Comp12626L2Odd)
    (hR : Comp12626Lie2TwoRest) : Comp12626Lie2Two := by
  intro Q _ K L P T v hQ h hK
  rcases hK with hK | hK | hK | hK | hK
  · exact not_psl32_of_l2Odd h2 hQ h hK
  · exact not_psl42 hQ h hK
  · exact hR Q K L P T v hQ h (Or.inl hK)
  · exact hR Q K L P T v hQ h (Or.inr (Or.inl hK))
  · exact hR Q K L P T v hQ h (Or.inr (Or.inr hK))

end CFSG.Quasithin.H13.S126C
