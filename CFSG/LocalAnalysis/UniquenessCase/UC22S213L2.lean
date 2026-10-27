module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S213Rest4
import CFSG.LocalAnalysis.UniquenessCase.UC22S213CenterZ
import CFSG.LocalAnalysis.UniquenessCase.UC22S213PrimeRank
import CFSG.LocalAnalysis.UniquenessCase.UC22P20p
import CFSG.LocalAnalysis.UniquenessCase.UC22P21k
import CFSG.LocalAnalysis.UniquenessCase.UC22P22qe
import CFSG.LocalAnalysis.UniquenessCase.UC22OddPRank
import CFSG.GH74.GLS.Stage2.Final.ECInterGriess

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open Subgroup
open CFSG.Blueprint (LieModel)
open CFSG.Blueprint.Multiplier (genericOrders exceptionalOrders)

variable {G : Type} [Group G] [Finite G]

@[expose] def S21_3ClosedL2 (L : Subgroup G) : Prop :=
  ∃ p e : ℕ, p.Prime ∧ p ^ e ≠ 9 ∧ LieModel (BarInf L) .PSL 2 p e

theorem uc22s213_center_bar2_eq_bot_of_psl2_two_three (hGA : GriessAllModelsStatement)
    {M L : Subgroup G} (hL : L ∈ calC M) {p e : ℕ} (hp : p = 2 ∨ p = 3) (h9 : p ^ e ≠ 9)
    (hX : LieModel (BarInf L) .PSL 2 p e) : center (Bar2 L) = ⊥ := by
  obtain ⟨φ⟩ := uc22p21k_barInf_equiv_of_calC hL
  have hdvd := CFSG.RankThree.PartOne.card_center_dvd_of_model hGA
    (CFSG.Quasithin.A3.isQuasisimple_iff_open.2 hL.2.2)
    ((CFSG.Blueprint.LieModel.of_mulEquiv φ hX).statedClassicalModel (by decide))
  have hgen : genericOrders .PSL 2 p e = (Nat.gcd 2 (p ^ e - 1), 1) := rfl
  have he : 1 ≤ e := hX.admissible.2.1
  have h2 : Nat.card (center (Bar2 L)) ∣ 2 := by
    refine hdvd.trans ?_
    rcases hp with rfl | rfl
    ·
      have hg : Nat.gcd 2 (2 ^ e - 1) = 1 :=
        Nat.Coprime.gcd_eq_one (Nat.coprime_two_left.mpr (Nat.Even.sub_odd Nat.one_le_two_pow
          ((Nat.even_pow' (by omega)).mpr even_two) odd_one))
      have hx : exceptionalOrders .PSL 2 2 e = (2, 1) ∨ exceptionalOrders .PSL 2 2 e = (1, 1) := by
        unfold exceptionalOrders
        split <;> simp_all
      rcases hx with hx | hx <;> simp only [hgen, hx, hg, mul_one, one_mul, dvd_refl, one_dvd]
    · rcases CFSG.GH74.GLS.Stage2.Final.ECInterGriess.exceptionalOrders_psl2 (p := 3) (f := e)
          (by norm_num) with hexc | ⟨-, rfl, -⟩
      · simp only [hgen, hexc, mul_one]
        exact Nat.gcd_dvd_left _ _
      · exact absurd (by norm_num) h9
  have hodd : Odd (Nat.card (center (Bar2 L))) := uc22p20p_odd_center_bar2 ↥L
  rcases (Nat.dvd_prime Nat.prime_two).1 h2 with h1 | h1
  · exact Subgroup.eq_bot_of_card_eq _ h1
  · rw [h1] at hodd
    exact absurd hodd (by decide)

theorem uc22s213_false_of_closedL2 (hGA : GriessAllModelsStatement) {M L : Subgroup G}
    (hL : L ∈ calC M) (h : S21_3ClosedL2 L) (hZ : ¬ S21_3ClosedZ L) (hthin : ¬ F08.Thin8 L)
    (h3 : CFSG.Open.pRank 3 L ≤ 2) : False := by
  obtain ⟨p, e, hp, h9, hX⟩ := h
  obtain ⟨-, he, -, h22, h23⟩ := hX.admissible
  have hpe : p < 5 ∨ e = 1 := by
    rcases lt_or_ge p 5 with h5 | h5
    · exact Or.inl h5
    · refine Or.inr (by_contra fun he1 => hZ ?_)
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
        ⟨p, e, hp, h5, by omega, hX⟩))))))
  have hZ1 : center (Bar2 L) = ⊥ := by
    rcases lt_or_ge p 5 with hp5 | hp5
    · refine uc22s213_center_bar2_eq_bot_of_psl2_two_three hGA hL ?_ h9 hX
      interval_cases p <;> first | (left; rfl) | (right; rfl) | (norm_num at hp)
    · exact uc22s213_center_bar2_eq_bot_of_psl2 hGA hL hp5 hX
  have hrank : ∀ r : ℕ, r.Prime → r ≠ 2 →
      CFSG.Open.pRank r (⊤ : Subgroup (BarInf L)) = CFSG.Open.pRank r L := fun r hr hr2 =>
    uc22s213_pRank_barInf_of_prime hL.2.2 hr hr2 (by rw [hZ1, card_bot]; exact hr.not_dvd_one)
  by_cases hp3 : p = 3
  ·
    subst hp3
    have he3 : 3 ≤ e := by
      rcases (show e = 1 ∨ e = 2 ∨ 3 ≤ e by omega) with rfl | rfl | he3
      · exact absurd rfl h23
      · exact absurd rfl h9
      · exact he3
    haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    obtain ⟨P, hP⟩ := CFSG.ABGLocalTools.exists_isSylowOf 3 (⊤ : Subgroup (BarInf L))
    obtain ⟨hPel, hPc⟩ := uc22p22q_psl2_sylow_elem Nat.prime_three (by norm_num) hX hP
    have hr := CFSG.SectionRank.le_pRank (by norm_num) le_top hPel hPc
    rw [hrank 3 Nat.prime_three (by norm_num)] at hr
    omega
  apply hthin
  intro r hr hr2
  rw [← hrank r hr hr2]
  by_cases hp2 : p = 2
  · subst hp2
    exact pRank_le_one_of_isL2_or_isSz (Or.inl hX) hr hr2
  · have hp5 : 5 ≤ p := by
      by_contra h5
      have h5' : p < 5 := by omega
      have := hp.two_le
      interval_cases p <;> first | omega | (norm_num at hp)
    have he1 : e = 1 := hpe.resolve_left (by omega)
    subst he1
    exact CFSG.QuasithinUnique.Id2519.pRank_le_one_psl_two_prime hp (by omega)
      (hX.statedClassicalModel (by decide)) hr hr2

end CFSG.LocalAnalysis.UniquenessCase.UC22
