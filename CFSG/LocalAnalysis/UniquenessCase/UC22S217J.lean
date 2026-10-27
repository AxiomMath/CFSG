module

public import CFSG.LocalAnalysis.UniquenessCase.UC22P2213TDefs
public import CFSG.LocalAnalysis.UniquenessCase.UC6S846e
public import CFSG.LocalAnalysis.UniquenessCase.UC6R
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.R76Sig
import CFSG.LocalAnalysis.UniquenessCase.UC22S217JPair
import CFSG.LocalAnalysis.UniquenessCase.UC22InE229NSE
import CFSG.LocalAnalysis.UniquenessCase.UC22P22i
import CFSG.LocalAnalysis.UniquenessCase.UC22P21k
import CFSG.LocalAnalysis.UniquenessCase.UC6R77E2
import CFSG.LocalAnalysis.UniquenessCase.UC6Syl
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.JankoOne
public import CFSG.LocalAnalysis.UniquenessCase.UC6S846c

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)

variable {G : Type} [Group G] [Finite G]

theorem uc22s217j_seven_facts {Y : Type} [Group Y] [Finite Y] {W : Subgroup Y}
    (hW : Nat.card W = 175560) {p : ℕ} (hp : ¬ p ∣ 175560) :
    CFSG.Open.pRank 7 W ≤ 1 ∧ 7 ∣ Nat.card W ∧ ¬ p ∣ Nat.card (Sylow 7 ↥W) := by
  haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  refine ⟨?_, by rw [hW]; norm_num, fun h => hp ?_⟩
  · obtain ⟨E, hEW, -, hE⟩ := CFSG.SectionRank.exists_pRank (by norm_num : 1 < 7) W
    have hdvd : 7 ^ CFSG.Open.pRank 7 W ∣ 175560 := by
      rw [← hW, ← hE]
      exact Subgroup.card_dvd_of_le hEW
    by_contra h2
    have h49 := (pow_dvd_pow 7 (by omega : 2 ≤ CFSG.Open.pRank 7 W)).trans hdvd
    norm_num at h49
  · obtain ⟨P⟩ := (inferInstance : Nonempty (Sylow 7 ↥W))
    rw [← hW]
    exact h.trans ((Sylow.card_dvd_index P).trans (Subgroup.index_dvd_card _))

theorem uc22s217j_exists_elemAbelian_of_isJ1 {M L A₀ : Subgroup G} (hL : L ∈ calC M)
    (hc2 : (conjSetOf M L).ncard = 2) (hJ : IsJ1 (Bar2 L)) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hpL : ¬ p ∣ Nat.card L) (hA₀M : A₀ ≤ M) (hA₀ : IsPGroup p A₀) :
    ∃ E : Subgroup G, E ≤ M ∧ IsElemAbelian 7 E ∧ Nat.card E = 7 ^ 2 ∧
      A₀ ≤ normalizer (E : Set G) ∧
      ∀ R : Subgroup G, R ≤ M → IsPGroup 7 R → E ≤ R → E ≤ centralizer (R : Set G) := by
  obtain ⟨hcard, hsimple, -⟩ := kJ1_holds (Bar2 L) hJ
  haveI := hsimple
  have hpJ : ¬ p ∣ 175560 := by
    rw [← hcard]
    exact fun h => hpL (h.trans (Subgroup.card_quotient_dvd_card _))
  have hp7 : p ≠ 7 := by
    rintro rfl
    exact hpJ (by norm_num)
  exact uc22s217j_exists_elemAbelian_of_pair hL hc2 (uc22p21k_center_eq_bot hL.2.2) hp
    (by norm_num) hp2 (by norm_num) hp7
    (fun W e => uc22s217j_seven_facts (by rw [← Nat.card_congr e.toEquiv, hcard]) hpJ) hA₀M hA₀

theorem uc22s217j_not_sp_seven {D : Data G} {Ch : Choice2011 G} (h211 : S21_1 D Ch)
    (h1930 : H1930 D) (c : Ctx21 D Ch) (hn3 : c.n = 3) : ¬ IsStronglyPEmbedded 7 D.M := by
  obtain ⟨b, hb, hbo⟩ := uc22p22i_exists_elt_of_mem_piSet (B := c.B0) (r := 7) (by
    rw [c.hpi, hn3, etaSet, Set.mem_setOf_eq]
    exact ⟨by norm_num, by norm_num⟩)
  have hle : c.B0 ≤ oPi (etaSet c.n) c.B0 := by
    refine le_iSup₂_of_le c.B0 ⟨le_rfl, ?_, c.hpi.subset⟩ le_rfl
    rw [Subgroup.subgroupOf_self]
    exact Subgroup.normal_top
  have hα : oPi (etaSet c.n) c.B0 ≤ normalizer (D.T : Set G) :=
    c.hα 0 c.n (by rw [hn3]; decide) (by simp)
  exact uc22ine229_not_sp_of_mem_normalizer h211 h1930 c (by norm_num) (by norm_num)
    (hα (hle hb)) hbo

theorem s21_17J_of_conclusion76 (D : Data G) (Ch : Choice2011 G) (h211 : S21_1 D Ch)
    (hSg : UC6S846.SigmaStd D) (h614 : UC6.R6_14 D) (h76 : F07.R76Sig D) : S21_17J D Ch := by
  intro h1930 c L hL hc2 hJ hn3 p hp
  by_contra hpL
  obtain ⟨hpp, hp2⟩ := D.sig_prime p hp
  have hns : ¬ Group.IsSolvable ↥D.M := UC6S846.not_solvable_of_mem_calC hL
  have hnse := uc22s217j_not_sp_seven h211 h1930 c hn3
  have h7σ : 7 ∉ D.sig := fun h => hnse (UC6S846.sp_of_mem_sig hSg hns h)
  have hp7 : p ≠ 7 := by
    rintro rfl
    exact h7σ hp
  obtain ⟨A₀, hA₀M, hA₀el, hA₀card⟩ :=
    UC6S846.exists_elemAbelian_card_of_le_pRank hpp (hSg.three_le p hp)
  obtain ⟨E, hEM, hEel, hEcard, hA₀E, hEZ⟩ :=
    uc22s217j_exists_elemAbelian_of_isJ1 hL hc2 hJ hpp hp2 hpL hA₀M hA₀el.isPGroup
  haveI : Fact p.Prime := ⟨hpp⟩
  haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have hΓ : rankThreeGamma 1 7 E ≤ D.M := by
    have h3 := UC6S846.le_pRank' hpp (le_inf hA₀M hA₀E) hA₀el hA₀card
    exact UC6R77.rankThreeGamma_le_of_two_lt_pRank hp7
      (h76 p hp hp2 (UC6S846.sp_of_mem_sig hSg hns hp)) hEM hEel hEcard (by omega)
  obtain ⟨R, hR, hER⟩ := UC6.exists_isSylowOf_ge hEM hEel.isPGroup
  exact hnse (h614 (UC6S846.sig_subset_sig1 hSg hns) 7 (by norm_num) (by norm_num) h7σ R hR E
    (le_inf hER (hEZ R hR.le hR.isPGroup hER)) hEel hEcard hΓ)

end CFSG.LocalAnalysis.UniquenessCase.UC22
