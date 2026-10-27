module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154Std
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154AssemblyCNAFree
public import CFSG.GroupTheory.IsCyclicOfPRankLeOne
public import CFSG.GroupTheory.PRankZeroOfPrimeNotDvd
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154ThreeCovers

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

theorem s16h_pRank_three_eq_one_of_thin_cover (D : Data G)
    {V₀ V L : Subgroup G} (h : Setting16 D V₀ V L)
    (hcomp : IsComponentOf (lBar V₀ V h.hyp151.isElemAbelian L)
      (Mbar D.M V₀ V h.hyp151.isElemAbelian))
    {t : MulAut (Vtil V₀ V h.hyp151.isElemAbelian)}
    (hW : Conc4_136W (Mbar D.M V₀ V h.hyp151.isElemAbelian) t
      (lBar V₀ V h.hyp151.isElemAbelian L))
    (hthin : ∀ q : ℕ, q.Prime → q ≠ 2 →
      CFSG.Open.pRank q (lBar V₀ V h.hyp151.isElemAbelian L) ≤ 1)
    (h3 : 3 ∣ Nat.card (lBar V₀ V h.hyp151.isElemAbelian L))
    {K : Subgroup G} (hK : K ∈ calC D.M)
    (hbar : barSub V₀ V h.hyp151.isElemAbelian K =
      lBar V₀ V h.hyp151.isElemAbelian L) :
    CFSG.Open.pRank 3 K = 1 := by
  have hV := h.hyp151.isElemAbelian
  rw [← hbar] at hthin
  haveI : Finite (MulAut (Vtil V₀ V hV)) :=
    Finite.of_injective
      (fun e : MulAut (Vtil V₀ V hV) => (e : Vtil V₀ V hV → Vtil V₀ V hV))
      (fun _ _ hh => MulEquiv.ext (congrFun hh))
  have hne : barSub V₀ V hV K ≠ ⊥ := by
    rw [hbar]
    exact (Subgroup.nontrivial_iff_ne_bot (lBar V₀ V hV L)).mp
      (CFSG.ComponentClassification.Quasisimple.nontrivial hcomp.2.2)
  have hcyc : ∀ Q : Sylow 3 ↥(barSub V₀ V hV K),
      IsCyclic ↥(Q : Subgroup ↥(barSub V₀ V hV K)) := by
    intro Q
    have hrank : CFSG.Open.pRank 3 (⊤ : Subgroup ↥(barSub V₀ V hV K)) ≤ 1 := by
      rw [← CFSG.SectionRank.pRank_eq_pRank_top_subgroup (p := 3) (barSub V₀ V hV K)]
      exact hthin 3 Nat.prime_three (by norm_num)
    have hQrank : CFSG.Open.pRank 3
        (⊤ : Subgroup ↥(Q : Subgroup ↥(barSub V₀ V hV K))) ≤ 1 := by
      rw [← CFSG.SectionRank.pRank_eq_pRank_top_subgroup (p := 3)
        (Q : Subgroup ↥(barSub V₀ V hV K))]
      exact (CFSG.SectionRank.pRank_mono Nat.prime_three.one_lt
        (le_top : (Q : Subgroup ↥(barSub V₀ V hV K)) ≤ ⊤)).trans hrank
    exact CFSG.isCyclic_of_pRank_le_one Nat.prime_three (by norm_num) Q.isPGroup' hQrank
  have h3bar : 3 ∣ Nat.card ↥(barSub V₀ V hV K) := by
    rw [hbar]
    exact h3
  have hKle : K ≤ stabTil V₀ V :=
    (A3.subnormal_le hK.1).trans
      (le_stabTil h.hyp151.hyp125.pairFacts.le_normalizer
        h.hyp151.hyp125.pairFacts.le_normalizer₀)
  have h3K : 3 ∣ Nat.card K :=
    h3bar.trans (s16h_card_barSub_dvd V₀ V hV hKle)
  refine le_antisymm ?_ ?_
  · exact s16h_pRank_cover_le_one_of_cyclic_sylow D h.hyp151.hyp125 hK hne
      Nat.prime_three (by norm_num) hcyc
  · rw [CFSG.SectionRank.pRank_eq_pRank_top_subgroup (p := 3) K]
    exact CFSG.one_le_pRank_of_dvd_card Nat.prime_three h3K

theorem s16h_sig_dvd_or_strong_three_of_component (D : Data G) (S : s16h_Std D)
    (h880 : F08.R880 D) (h163 : R16_3FComp D) (hSchur : RSchur153)
    {V₀ V L : Subgroup G} (h : Setting16 D V₀ V L)
    (hcomp : IsComponentOf (lBar V₀ V h.hyp151.isElemAbelian L)
      (Mbar D.M V₀ V h.hyp151.isElemAbelian))
    {t : MulAut (Vtil V₀ V h.hyp151.isElemAbelian)}
    (ht : t ∈ Mbar D.M V₀ V h.hyp151.isElemAbelian)
    (ht2 : t ^ 2 = 1) (ht1 : t ≠ 1) (htr : rk ↥(commSub ⊤ (zpowers t)) ≤ 3)
    (hW : Conc4_136W (Mbar D.M V₀ V h.hyp151.isElemAbelian) t
      (lBar V₀ V h.hyp151.isElemAbelian L))
    (h3 : 3 ∣ Nat.card (lBar V₀ V h.hyp151.isElemAbelian L))
    (hs : 2 < s15 D.M V₀ V h.hyp151.isElemAbelian L) :
    (∃ q : ℕ, q.Prime ∧ q ≠ 2 ∧ q ∈ D.sig ∧
        q ∣ Nat.card (lBar V₀ V h.hyp151.isElemAbelian L)) ∨
      CFSG.RankThree.PartOne.IsStronglyPEmbedded 3 D.M := by
  have hV := h.hyp151.isElemAbelian
  by_cases hthin : ∀ q : ℕ, q.Prime → q ≠ 2 →
      CFSG.Open.pRank q (lBar V₀ V hV L) ≤ 1
  · obtain ⟨K, hK, hbar⟩ :=
      s16h_exists_cover D S.h127 S.h119 h.hyp151.hyp125 hcomp
    exact Or.inr (s16h_stronglyEmbedded_of_pRank_one_cover D S.h82 h hs hK hbar
      (s16h_pRank_three_eq_one_of_thin_cover D h hcomp hW hthin h3 hK hbar))
  · obtain ⟨q, hqprime, hq2, hqle⟩ : ∃ q : ℕ, q.Prime ∧ q ≠ 2 ∧
        ¬ CFSG.Open.pRank q (lBar V₀ V hV L) ≤ 1 := by
      obtain ⟨q, hq⟩ := not_forall.1 hthin
      obtain ⟨hqprime, hq'⟩ := not_imp.1 hq
      obtain ⟨hq2, hqle⟩ := not_imp.1 hq'
      exact ⟨q, hqprime, hq2, hqle⟩
    exact Or.inr (s16h_nonthin_dichotomy_free D S.h127 S.h119 h880 h163 hSchur h (by omega) ht
      ht2 ht1 htr hW hcomp hqprime hq2 (by omega)).2

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
