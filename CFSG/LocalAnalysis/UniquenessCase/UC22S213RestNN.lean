module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S213Rest
public import CFSG.LocalAnalysis.UniquenessCase.UCFront08Use
public import CFSG.LocalAnalysis.UniquenessCase.UC6S846e
import CFSG.LocalAnalysis.UniquenessCase.UC22S213Inner
import CFSG.LocalAnalysis.UniquenessCase.UC22S213PrimeRank
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.ConjSetCard

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open Subgroup
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

@[expose] def S21_3RestNN (D : Data G) (Ch : Choice2011 G) : Prop :=
  H1930 D → ∀ c : Ctx21 D Ch, ∀ L ∈ calC D.M, ¬ D.M ≤ normalizer (L : Set G) →
    (∀ q : ℕ, q.Prime → q ≠ 2 → 2 ≤ CFSG.Open.pRank q L →
      q ∣ Nat.card (center (Bar2 L))) →
    ¬ F08.Thin8 L → CFSG.Open.pRank 3 L ≤ 2 →
    (IsStronglyPEmbedded 3 D.M → CFSG.Open.pRank 3 L ≤ 1) →
    ∀ a ∈ c.B, (orderOf a).Prime →
      (∀ p ∈ D.sig,
        CFSG.Open.pRank p (normalizer ((zpowers a : Subgroup G) : Set G) ⊓ D.M) ≤ 1) →
      ¬ CentralizesBar a L

theorem s21_3Rest_of_restNN {D : Data G} {Ch : Choice2011 G} (hσ : UC6S846.SigmaStd D)
    (h869N : F08.R869N D) (h : S21_3RestNN D Ch) : S21_3Rest D Ch := by
  intro hH c L hL hthin h3 hk1 a ha hpr hN haL
  have hodd : Odd (orderOf a) := uc22p21d_odd_orderOf_of_mem_calB1 c.hB ha
  have hLM : L ≤ D.M := hL.1.le
  have hr2 : orderOf a ≠ 2 := fun h2 => Nat.not_odd_iff_even.mpr even_two (h2 ▸ hodd)
  by_cases hMN : D.M ≤ normalizer (L : Set G)
  ·
    have hY := uc22p21d_sup_pCore_eq hpr hr2 (Nat.card_zpowers a) fun g hg =>
      uc22p21d_centralizesBar_of_mem_zpowers haL hg
    have hAB : zpowers a ≤ c.B := zpowers_le.mpr ha
    exact s21_2 D Ch hH c _ hAB (h869N L hLM hMN ⟨1, fun _ => L, fun _ => hL, by simp⟩ hthin _
      hpr hr2 (zpowers a) (hAB.trans (c.hle.trans c.hBM)) (Nat.card_zpowers a) hY)
  ·
    refine h hH c L hL hMN (fun q hq hq2 h2 => ?_) hthin h3 hk1 a ha hpr hN haL
    by_contra hZ
    have hqσ : q ∉ D.sig := fun hqs => by
      have := uc22s213_pRank_le_one_of_centralizesBar hLM hodd hpr haL hq hq2 (hN q hqs)
      omega
    obtain ⟨g, hg, hgN⟩ : ∃ g ∈ D.M, g ∉ normalizer (L : Set G) := by
      by_contra hc
      push Not at hc
      exact hMN hc
    have hne : L ≠ L.map (MulAut.conj g).toMonoidHom := fun he =>
      hgN (Subgroup.mem_normalizer_iff_map_conj_eq.mpr he.symm)
    have h4 := uc22s213_four_le_pRank_of_two_conj hL
      (PartOne.Section8.mem_conjSetOf_self D.M L) ⟨g, hg, rfl⟩ hne hq hq2 h2 hZ
    exact hqσ (hσ.four_mem q hq hq2 h4)

end CFSG.LocalAnalysis.UniquenessCase.UC22
