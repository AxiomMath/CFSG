module

public import CFSG.RankThree.PartOne.S10.Defs
public import CFSG.RankThree.PartOne.S9.StatementsSylow
import CFSG.RankThree.PartOne.S9.Top.Dichotomy
import CFSG.RankThree.PartOne.S9.Sylow.ExclusionRank
import CFSG.RankThree.OddKernel.ThreeComplementQuotient
public import CFSG.LocalAnalysis.SectionRank.PRank
public import CFSG.RankThree.GroupTheory.SteinbergBYRelativeCores
public import CFSG.RankThree.LocalRank.SelectorCases

public section

namespace CFSG.RankThree.PartOne.F106

open Subgroup CFSG CFSG.Assembly CFSG.Assembly.RankThreeEven CFSG.RankThree
  CFSG.RankThree.LocalRank CFSG.RankThree.GroupTheory CFSG.LocalAnalysis.ComponentInitial

theorem false_of_large_prime (hCVD : CoreVanishingDichotomy) {G : Type} [Group G] [Finite G]
    {p : ℕ} {A : Subgroup G} (h : SteinbergBM.SectionTenSetup G p A) (hp7 : p ≤ 7) {q n : ℕ}
    (hq : q.Prime) (hq7 : 7 < q) (hn : 4 ≤ n) {D : Subgroup G}
    (hDe : IsElementaryAbelian q D) (hDcard : Nat.card D = q ^ n) {r : G} (hr2 : orderOf r = 2)
    (hrank : CFSG.pRank q ↥(D ⊓ Subgroup.centralizer ({r} : Set G)) = 3) : False := by
  have hq1 : 1 < q := hq.one_lt
  have hq2 : q ≠ 2 := by omega
  have he : evenRank G = 3 := sectionTenSetup_evenRank_eq h
  have hrk : n ≤ CFSG.pRank q G := by
    have h1 := CFSG.SectionRank.le_pRank hq1 (le_top : D ≤ ⊤)
      ((CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian q D).mp hDe) hDcard
    have h2 : CFSG.pRank q G = CFSG.Open.pRank q (⊤ : Subgroup G) :=
      CFSG.SectionRank.pRank_eq_open_pRank_top q G
    omega
  have hr1 : r ≠ 1 := fun h1 => by
    rw [h1, orderOf_one] at hr2
    omega
  obtain ⟨E', hE'le, hE', hE'card⟩ :=
    CFSG.SectionRank.exists_pRank hq1 (D ⊓ Subgroup.centralizer ({r} : Set G))
  have h3 : CFSG.Open.pRank q (D ⊓ Subgroup.centralizer ({r} : Set G)) = 3 := by
    have := assembly_pRank_eq hq (D ⊓ Subgroup.centralizer ({r} : Set G))
    rw [hrank] at this
    exact this
  rw [h3] at hE'card
  have hU : Subgroup.zpowers r ≠ ⊥ := fun h1 => hr1 (by
    rw [Subgroup.zpowers_eq_bot] at h1
    exact h1)
  have hU2 : IsPGroup 2 (Subgroup.zpowers r) := IsPGroup.of_card (n := 1) (by
    rw [Nat.card_zpowers, hr2]
    simp)
  have hE'N : E' ≤ Subgroup.normalizer ((Subgroup.zpowers r : Subgroup G) : Set G) := by
    refine le_trans ?_ (Subgroup.centralizer_le_normalizer _)
    intro x hx
    have hxC : x ∈ Subgroup.centralizer ({r} : Set G) := (hE'le hx).2
    rw [← SteinbergBY.centralizer_singleton_eq_centralizer_zpowers] at *
    exact hxC
  have h3le : 3 ≤ localRank q G :=
    Sec9Excl.le_localRank_of_normalizes hq1 hU hU2 hE'.1 hE'.2 hE'card
      (fun x hx => hE'N hx)
  have hlr : localRank q G = 3 :=
    le_antisymm ((CFSG.RankThree.OddKernel.localRank_le_evenRank hq hq2).trans he.le) h3le
  have hσ : q ∈ sigmaA G := by
    rw [rank_three_selector_of_large he ⟨q, hq, by omega, hlr⟩]
    exact ⟨hq, by omega, hlr⟩
  have hsec : Sec9Hyp G q :=
    { simple := h.1, nonabelian := h.2.1, kProper := sectionTenSetup_kProper h,
      charTwo := sectionTenSetup_charTwo h, evenRank_eq := he, prime := hq,
      three_lt := by omega, mem_sigma := hσ }
  have hgood : GoodGlobalRank G q := fun h7 => absurd h7 (by omega)
  have hstar : ∀ P' : Sylow q G, ∀ H : Subgroup G, IsTwoLocal H →
      ¬ aschCore 2 q (P' : Subgroup G) ≤ H := fun Q H hH hle =>
    Sec9Top.not_exists_twoLocal_aschCore_of_pRank_gt_three he hq hq2 (by omega) Q ⟨H, hH, hle⟩
  have hvan : SteinbergBY.AschVanishing G q := by
    intro A' hA' hAcard B hBA hBcard c hcA hc1
    have hApg : IsPGroup q A' := hA'.isPGroup q A'
    obtain ⟨P', hAP'⟩ := hApg.exists_le_sylow
    rcases hCVD G q hsec hgood A' hA' hAcard P' hAP' B hBA hBcard c hcA hc1 with
      ⟨-, H₀, hH₀, hle⟩ | ⟨hα, ⟨T, hT, hTA⟩, hodd⟩
    · exact absurd hle (hstar P' H₀ hH₀)
    · refine ⟨hα, ?_, hodd⟩
      have hcp : c ^ q = 1 := elemPow_eq_one_of_isElementaryAbelian c hcA
      rw [Sec9Top.inSubgroup_theta_normalizer_zpowers_eq hq hcp] at hT
      obtain ⟨S, hS⟩ := Sec9Top.exists_sylow_map_eq Nat.prime_two hT
      exact ⟨S, hS ▸ hTA⟩
  have hQ10 : q ∈ SteinbergBM.sectionTenPrimeSet G :=
    ⟨hq, by omega, hσ, hvan, E', (CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian q E').mpr
      hE', hE'card, Subgroup.zpowers r, hU, hU2, hE'N⟩
  have := h.2.2.2.2.2.2.2.2.2 ⟨q, hQ10, hq7⟩
  omega

end CFSG.RankThree.PartOne.F106
