module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S21rR3
public import CFSG.LocalAnalysis.UniquenessCase.UC22S21rHp
public import CFSG.LocalAnalysis.UniquenessCase.UC22S21rS1Eq

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup

variable {G : Type} [Group G] [Finite G]

theorem s21_22Use_of_s21_22R3_noCtx22 (D : Data G) (Ch : Choice2011 G) (st : Standing22 D)
    (hr77 : F07.R77Eq D) (he : CFSG.Open.evenRank G = 3) (h2118 : S21_18 D Ch)
    (h211 : S21_1 D Ch) (hR3 : S21_22R3 D Ch) : S21_22Use D Ch := by
  intro h1930 c H₁ hH₁ H₂ hH₂ hL hfX
  have hS1 := uc22s21rs1_hinf_commutator_le_eq D st hr77 hH₁ hH₂
    (fun X h1 h2 hF => hfX X h1 h2 (Or.inl hF))
  exact (hR3 h1930 c H₁ hH₁ H₂ hH₂ hL hfX hS1
    (s21_22U3_holds D Ch st h2118 h211 h1930 c H₁ hH₁ H₂ hH₂ hL hfX hS1)
    (s21_22Sig1_holds D Ch st.sigmaStd st.r6_1 h1930 c H₁ hH₁ H₂ hH₂ hL hfX hS1) he).elim

end CFSG.LocalAnalysis.UniquenessCase.UC22
