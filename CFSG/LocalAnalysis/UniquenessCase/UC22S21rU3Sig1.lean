module

public import CFSG.LocalAnalysis.UniquenessCase.UC22InE229N
public import CFSG.LocalAnalysis.UniquenessCase.UC22S13xa
public import CFSG.LocalAnalysis.UniquenessCase.UC22S21r8101U3
public import CFSG.LocalAnalysis.UniquenessCase.UC22Standing22
import CFSG.LocalAnalysis.UniquenessCase.UC22S21rU3b
import CFSG.LocalAnalysis.UniquenessCase.UC22S21rU3c
import CFSG.LocalAnalysis.UniquenessCase.UC22S21rU4Ctx21
import CFSG.LocalAnalysis.UniquenessCase.UC22S21rZ
public import CFSG.LocalAnalysis.UniquenessCase.UC22S21rU

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)
open CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7 (Conclusion76)
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

@[expose] def S21_22Sig1 (D : Data G) (Ch : Choice2011 G) : Prop :=
  H1930 D → ∀ c : Ctx21 D Ch, ∀ H₁ ∈ hSet D.T D.M, ∀ H₂ ∈ hSet D.T D.M, c.L0 ≤ H₁ ⊓ H₂ →
    (∀ X : Subgroup G, X ≤ D.M → D.T ≤ X →
      (F12.InF 1 (⊤ : Subgroup (Bar2 X)) ∨ Group.IsSolvable ↥X) →
      (X : Set G) = ((H₁ ⊓ X : Subgroup G) : Set G) * ((H₂ ⊓ X : Subgroup G) : Set G)) →
    ⁅Hinf D.M, oTwoFOf D.M⁆ ≤ CFSG.Open.pCoreOf 2 D.M → D.sig = D.sig1

theorem s21_22U3_of_s21_22Sig1 (D : Data G) (Ch : Choice2011 G) (st : Standing22 D)
    (h2118 : S21_18 D Ch) (h211 : S21_1 D Ch) (hsig : S21_22Sig1 D Ch) : S21_22U3 D Ch := by
  intro h1930 c H₁ hH₁ H₂ hH₂ hL hfX hS1 p hp
  have hsp : IsStronglyPEmbedded p D.M :=
    st.sigmaStd.sig1_sp p (hsig h1930 c H₁ hH₁ H₂ hH₂ hL hfX hS1 ▸ hp)
  have hR : CFSG.perfectResidual (Bar2 D.M) = CFSG.layer (Bar2 D.M) :=
    (uc22p21c_Hinf_eq_iff D.M).1 (h2118 h1930 c hS1)
  have hSs : Group.IsSolvable ↥(centE D.M) := uc22s21ru3c_isSolvable_centralizer hR
  obtain ⟨Y, hTY, hYM, hYs, hZY⟩ := uc22s21ru3c_exists_Y D hSs
  have hnd : ¬ p ∣ Nat.card Y :=
    uc22s21ru3b_not_dvd_card D Ch st h211 h1930 c hH₁ hH₂
      (fun X h1 h2 hF => hfX X h1 h2 (Or.inl hF)) hp hsp hTY hYM hYs
  exact uc22s21ru3c_pRank_eq_zero (D.sig_prime p hp).1 hZY hnd

theorem s21_22Use_of_s21_22Sig1
    (D : Data G) (Ch : Choice2011 G) (st : Standing22 D) (hr77 : F07.R77E4 D)
    (he : 3 < CFSG.Open.evenRank G) (h211 : S21_1 D Ch) (h2118 : S21_18 D Ch)
    (h21EB : S21_21EB D Ch) (h8E : S21_8E D Ch) (h9 : S21_9N D Ch) (h17 : S21_17 D Ch)
    (hn3 : H1930 D → ∀ c : Ctx21 D Ch, 3 ≤ c.n) (h869P : F08.R869NPair D)
    (h8100E : R8100E D)
    (h76 : ∀ p ∈ D.sig, IsStronglyPEmbedded p D.M → Conclusion76 D.M p)
    (h614 : UC6.R6_14 D) (h847 : F08.R847 D) (h869 : F08.R869NS5 D) (hGL : GL3Excl.GL3Excl)
    (hU : R8101U3 D) (hsig : S21_22Sig1 D Ch) : S21_22Use D Ch := by
  intro h1930 c H₁ hH₁ H₂ hH₂ hL hfX
  exact s21_22Use_of_s21_22U3_U4 D Ch st hr77 he h21EB
    (uc22m57_exists_ctx21_ne_bot_ctx21 c (hn3 h1930 c)) h8E h9 h17
    (s21_22U3_of_s21_22Sig1 D Ch st h2118 h211 hsig)
    (s21_22U4_of_U4BC_ctx21 D Ch h869P h8100E hn3
      (s21_22U4BC_of_r8101U3 h211 st.sigmaStd st.dataExt.four_le h76 h614 h847 h869 hGL hn3 hU))
    h1930 c H₁ hH₁ H₂ hH₂ hL hfX

end CFSG.LocalAnalysis.UniquenessCase.UC22
