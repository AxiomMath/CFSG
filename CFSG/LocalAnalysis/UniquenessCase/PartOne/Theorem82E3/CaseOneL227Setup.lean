module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.CaseOneLbar
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.KeyLemma
import CFSG.Foundations.SteinbergCADefinitionNodes
import CFSG.GH74.Uniqueness.SU.SU1Basic
import CFSG.LocalAnalysis.SectionRank.AmbientRank

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3

open CFSG.Open
open CFSG.Blueprint (LieModel)
open CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82 (K4a)
open CFSG.LocalAnalysis.UniquenessCase.UC22 (Data)
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {D : Data G}

namespace Ctx82E3

theorem two_le_pRank_map_ker_of_L227 (c : Ctx82E3 D)
    (h811 : CFSG.Yardstones.Mf4cdcdf2e013.QuasisimpleModOTwo c.L) (hK4a : K4a)
    (h227 : CFSG.Blueprint.LieModel (c.Lbar ⧸ Subgroup.center c.Lbar) .PSL 2 3 3) {p : ℕ}
    (hp : p ∈ D.sig) :
    2 ≤ CFSG.Open.pRank p ((CFSG.GroupTheory.conjModPCore 2 c.L D.M c.le_normalizer_L).ker.map
      D.M.subtype) := by
  have hq : CFSG.IsQuasisimple c.Lbar :=
    (CFSG.Foundations.SteinbergCA.quasisimple_iff c.Lbar).2.2.1.mpr
      (isQuasisimple_lbar c h811)
  obtain ⟨-, -, -, haut⟩ := hK4a c.Lbar hq (odd_card_center_lbar c) h227
  have haut' : CFSG.pRank p (⊤ : Subgroup (MulAut c.Lbar)) ≤ 1 :=
    haut p (D.sig_prime p hp).1 (c.five_le_of_mem_sigma hp)
  rw [CFSG.SectionRank.pRank_coe_eq_openPRank] at haut'
  have hrange : CFSG.Open.pRank p
      (CFSG.GroupTheory.conjModPCore 2 c.L D.M c.le_normalizer_L).range ≤ 1 :=
    (CFSG.SectionRank.pRank_mono (D.sig_prime p hp).1.one_lt le_top).trans haut'
  have hrank := CFSG.GroupTheory.pRank_le_pRank_map_ker_add_pRank_range
    (p := 2) (q := p) (D.sig_prime p hp).1 c.L D.M c.le_normalizer_L
  have hM3 : 3 ≤ CFSG.Open.pRank p D.M := c.three_le p hp
  omega

theorem normalizer_le_of_L227 (c : Ctx82E3 D)
    (h811 : CFSG.Yardstones.Mf4cdcdf2e013.QuasisimpleModOTwo c.L) (hK4a : K4a)
    (h227 : CFSG.Blueprint.LieModel (c.Lbar ⧸ Subgroup.center c.Lbar) .PSL 2 3 3) {p : ℕ}
    (hp : p ∈ D.sig)
    (h76 : CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.Conclusion76 D.M p)
    {P : Subgroup G} (hP : CFSG.ABGLocalTools.IsSylowOf 3 P D.M) {Y : Subgroup G}
    (hY : Y ≤ P ⊓ c.L) (hY1 : Y ≠ ⊥) : Subgroup.normalizer (Y : Set G) ≤ D.M := by
  have h2 := two_le_pRank_map_ker_of_L227 c h811 hK4a h227 hp
  obtain ⟨R, hR_le, hR, hRcard⟩ :=
    CFSG.GH74.Uniqueness.SU.SU1.exists_isElemAbelian_of_le_pRank (p := p)
      (D.sig_prime p hp).1 (k := 2) h2
  have hRM : R ≤ D.M := hR_le.trans (Subgroup.map_subtype_le _)
  have hcomm : ⁅c.L, R⁆ ≤ CFSG.Open.pCoreOf 2 c.L :=
    (CFSG.GroupTheory.le_map_ker_conjModPCore_iff_commutator 2 c.L D.M R
      c.le_normalizer_L hRM).mp hR_le
  exact normalizer_le_of_commutator_le c hp h76 hP hRM hR.isPGroup
    (CFSG.SectionRank.le_pRank (D.sig_prime p hp).1.one_lt (le_refl R) hR hRcard) hcomm hY hY1

theorem exists_not_mem_L_of_L227 (c : Ctx82E3 D)
    (h811 : CFSG.Yardstones.Mf4cdcdf2e013.QuasisimpleModOTwo c.L) (hK4a : K4a)
    (h227 : CFSG.Blueprint.LieModel (c.Lbar ⧸ Subgroup.center c.Lbar) .PSL 2 3 3) {p : ℕ}
    (hp : p ∈ D.sig)
    (h76 : CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.Conclusion76 D.M p)
    {P : Subgroup G} (hP : CFSG.ABGLocalTools.IsSylowOf 3 P D.M) :
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
  have h2 := two_le_pRank_map_ker_of_L227 c h811 hK4a h227 hp
  omega

end Ctx82E3

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3
