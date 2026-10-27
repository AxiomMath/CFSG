module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.CaseOneLbar
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.KeyLemma
import CFSG.Foundations.SteinbergCADefinitionNodes
import CFSG.GH74.Uniqueness.SU.SU1Basic
import CFSG.LocalAnalysis.SectionRank.AmbientRank

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82

open CFSG.Open
open CFSG.Blueprint (LieModel)
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

namespace Counterexample4

theorem three_le_pRank_map_ker_of_L227 (c : Counterexample4 G)
    (h811 : CFSG.Yardstones.Mf4cdcdf2e013.QuasisimpleModOTwo c.L) (hK4a : K4a)
    (h227 : CFSG.Blueprint.LieModel (c.Lbar ⧸ Subgroup.center c.Lbar) .PSL 2 3 3) {p : ℕ}
    (hp : p ∈ CFSG.Open.uniqueFourSigma c.S.M) :
    3 ≤ CFSG.Open.pRank p ((CFSG.GroupTheory.conjModPCore 2 c.L c.S.M c.le_normalizer_L).ker.map
      c.S.M.subtype) := by
  have hq : CFSG.IsQuasisimple c.Lbar :=
    (CFSG.Foundations.SteinbergCA.quasisimple_iff c.Lbar).2.2.1.mpr
      (isQuasisimple_lbar c h811)
  obtain ⟨-, -, -, haut⟩ := hK4a c.Lbar hq (odd_card_center_lbar c) h227
  have haut' : CFSG.pRank p (⊤ : Subgroup (MulAut c.Lbar)) ≤ 1 :=
    haut p hp.1.1 (c.five_le_of_mem_sigma hp)
  rw [CFSG.SectionRank.pRank_coe_eq_openPRank] at haut'
  have hrange : CFSG.Open.pRank p
      (CFSG.GroupTheory.conjModPCore 2 c.L c.S.M c.le_normalizer_L).range ≤ 1 :=
    (CFSG.SectionRank.pRank_mono hp.1.1.one_lt le_top).trans haut'
  have hrank := CFSG.GroupTheory.pRank_le_pRank_map_ker_add_pRank_range
    (p := 2) (q := p) hp.1.1 c.L c.S.M c.le_normalizer_L
  have hM4 : 4 ≤ CFSG.Open.pRank p c.S.M := c.four_le_pRank_of_mem_sigma hp
  omega

theorem normalizer_le_of_L227 (c : Counterexample4 G)
    (h811 : CFSG.Yardstones.Mf4cdcdf2e013.QuasisimpleModOTwo c.L) (hK4a : K4a)
    (h227 : CFSG.Blueprint.LieModel (c.Lbar ⧸ Subgroup.center c.Lbar) .PSL 2 3 3) {p : ℕ}
    (hp : p ∈ CFSG.Open.uniqueFourSigma c.S.M)
    (h76 : CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.Conclusion76 c.S.M p)
    {P : Subgroup G} (hP : CFSG.ABGLocalTools.IsSylowOf 3 P c.S.M) {Y : Subgroup G}
    (hY : Y ≤ P ⊓ c.L) (hY1 : Y ≠ ⊥) : Subgroup.normalizer (Y : Set G) ≤ c.S.M := by
  have h3 := three_le_pRank_map_ker_of_L227 c h811 hK4a h227 hp
  have h2 : 2 ≤ CFSG.Open.pRank p
      ((CFSG.GroupTheory.conjModPCore 2 c.L c.S.M c.le_normalizer_L).ker.map
        c.S.M.subtype) := by omega
  obtain ⟨R, hR_le, hR, hRcard⟩ :=
    CFSG.GH74.Uniqueness.SU.SU1.exists_isElemAbelian_of_le_pRank (p := p) hp.1.1 (k := 2) h2
  have hRM : R ≤ c.S.M := hR_le.trans (Subgroup.map_subtype_le _)
  have hcomm : ⁅c.L, R⁆ ≤ CFSG.Open.pCoreOf 2 c.L :=
    (CFSG.GroupTheory.le_map_ker_conjModPCore_iff_commutator 2 c.L c.S.M R
      c.le_normalizer_L hRM).mp hR_le
  exact normalizer_le_of_commutator_le c hp h76 hP hRM hR.isPGroup
    (CFSG.SectionRank.le_pRank hp.1.1.one_lt (le_refl R) hR hRcard) hcomm hY hY1

theorem exists_not_mem_L_of_L227 (c : Counterexample4 G)
    (h811 : CFSG.Yardstones.Mf4cdcdf2e013.QuasisimpleModOTwo c.L) (hK4a : K4a)
    (h227 : CFSG.Blueprint.LieModel (c.Lbar ⧸ Subgroup.center c.Lbar) .PSL 2 3 3) {p : ℕ}
    (hp : p ∈ CFSG.Open.uniqueFourSigma c.S.M)
    (h76 : CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.Conclusion76 c.S.M p)
    {P : Subgroup G} (hP : CFSG.ABGLocalTools.IsSylowOf 3 P c.S.M) :
    ∃ y ∈ P, y ∉ c.L ∧ orderOf y = 3 := by
  by_contra h
  have hΩ : ∀ x ∈ P, x ^ 3 = 1 → x ∈ c.L := by
    intro x hxP hx3
    by_contra hxL
    have hx1 : x ≠ 1 := by
      rintro rfl
      exact hxL c.L.one_mem
    have hdvd : orderOf x ∣ 3 := orderOf_dvd_of_pow_eq_one hx3
    have hx3' : orderOf x = 3 := by
      rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h1 | h3
      · exact absurd (orderOf_eq_one_iff.mp h1) hx1
      · exact h3
    exact h ⟨x, hxP, hxL, hx3'⟩
  have hle := pRank_map_ker_le_one_of_forall_pow_eq_one c hp h76 hP hΩ
  have h3 := three_le_pRank_map_ker_of_L227 c h811 hK4a h227 hp
  omega

end Counterexample4

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82
