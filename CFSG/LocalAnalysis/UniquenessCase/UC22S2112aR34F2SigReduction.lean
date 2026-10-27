module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S2112aR34Sig
public import CFSG.LocalAnalysis.UniquenessCase.UC22S2112aR34LFDefs
import CFSG.LocalAnalysis.UniquenessCase.UC22S2112aR34F2
import CFSG.LocalAnalysis.UniquenessCase.UC22S218GChain
public import CFSG.LocalAnalysis.UniquenessCase.UC6Inst
public import CFSG.LocalAnalysis.UniquenessCase.UC22S214U
import CFSG.LocalAnalysis.UniquenessCase.UC6S846h

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup
open CFSG.Blueprint (LieModel)
open CFSG.Yardstones.Mf4cdcdf2e013 (Standing4 Setup4)

variable {G : Type} [Group G] [Finite G]

@[expose] def S21_12aFR34F2SigExc (D : Data G) (Ch : Choice2011 G) : Prop :=
  H1930 D → ∀ c : Ctx21 D Ch, ∀ L ∈ calC D.M, ∀ p : ℕ, p.Prime → p ≠ 2 → p ∉ D.sig →
    7 ≤ p →
    (LieModel (BarInf L) .PSp 2 p 1 ∨ LieModel (BarInf L) .G2 0 p 1) →
    (∀ f : ℕ, ¬ LieModel (BarInf L) .PSL 2 p f) →
    (∀ b ∈ c.B0, CentralizesBar b L → b = 1) → False

theorem s21_12aFR34F2Sig_of_exc {D : Data G} {Ch : Choice2011 G}
    (hσ : UC6S846.SigmaStd D) (hExc : S21_12aFR34F2SigExc D Ch) :
    S21_12aFR34F2Sig D Ch := by
  intro hH c L hL p hp hp2 hpσ t n f hadm ht hq hX hno hfaith
  obtain ⟨hA1, hA3, hRee⟩ := uc22s2112r34_funTwoType_ne ht
  have hA2 : ¬ ((t = .PSL ∨ t = .PSU) ∧ n = 3 ∧ f = 1) := fun h => hA3 ⟨h.1, h.2.1⟩
  have h5 : 5 ≤ p ^ f := by omega
  have hpN : ¬ p ∣ Nat.card ↥(CFSG.solvableRadical ↥L) :=
    not_dvd_card_solvableRadical hL.2.2 hp hp2
      (uc22s2112r34_not_dvd_center_char hL hp hp2 hRee hX (Or.inl ⟨h5, hA1⟩))
  obtain ⟨-, h4⟩ := uc22s2112r34_pRank_of_lieModel hp hp2 hX hA1 hA2 hRee hpN
  rcases h4 with ⟨hexc, hf1⟩ | h4
  · have h7 : 7 ≤ p := by
      rw [hf1, pow_one] at hq
      exact hq
    rcases hexc with ⟨rfl, rfl⟩ | rfl
    · subst f
      exact (hExc hH c L hL p hp hp2 hpσ h7 (Or.inl hX) hno hfaith).elim
    · subst f
      have hn0 : n = 0 := hadm.2.2.1
      subst n
      exact (hExc hH c L hL p hp hp2 hpσ h7 (Or.inr hX) hno hfaith).elim
  · exact absurd (uc22s2112r34_sig_of_le_pRank hσ hL hp hp2 h4).1 hpσ

theorem s21_12aR34F2Sig_dataOfSetup4_of_exc (hS : Standing4 G)
    (hU : CFSG.Open.uniqueFourUnique G) (S : Setup4 G) :
    S21_12aFR34F2SigExc (UC6.dataOfSetup4 hS hU S)
        (Choice214U (UC6.dataOfSetup4 hS hU S)) →
      S21_12aFR34F2Sig (UC6.dataOfSetup4 hS hU S)
        (Choice214U (UC6.dataOfSetup4 hS hU S)) :=
  s21_12aFR34F2Sig_of_exc (UC6S846.sigmaStd_dataOfSetup4 hS hU S)

end CFSG.LocalAnalysis.UniquenessCase.UC22

end
