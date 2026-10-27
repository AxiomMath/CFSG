module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.Core
import CFSG.GroupTheory.PGroup.ElemAbelianSq
import CFSG.LocalAnalysis.AGLEmbeddingD2.Escape
import CFSG.LocalAnalysis.StronglyEmbedded.PSubgroups
import CFSG.LocalAnalysis.UniquenessCase.UC6Syl
import CFSG.RankThree.PartOne.S12.Sec15Frattini

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.R72

open CFSG.Open
open CFSG.Yardstones.Mf4cdcdf2e013 (Standing4 Setup4 PartIAt TheoremCAt)
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)

variable {G : Type} [Group G] [Finite G]

theorem normalizer_le_of_theoremCAt {M : Subgroup G} (hC : TheoremCAt M) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hsp : IsStronglyPEmbedded p M) :
    ∀ D : Subgroup G, D ≠ ⊥ → IsPGroup 2 D →
      2 ≤ CFSG.Open.pRank p (Subgroup.normalizer (D : Set G) ⊓ M) →
      Subgroup.normalizer (D : Set G) ≤ M := by
  intro D hD hD2 h2
  obtain ⟨E, hE, hEel, hEcard⟩ :=
    CFSG.SectionRank.exists_pRank hp.one_lt (Subgroup.normalizer (D : Set G) ⊓ M)
  have hEM : E ≤ M := hE.trans inf_le_right
  exact hC p hp hp2 E hEM hEel.isPGroup
    (h2.trans (CFSG.SectionRank.le_pRank hp.one_lt le_rfl hEel hEcard))
    (hsp.rankThreeGamma_one_le_of_le hp hEel.isPGroup hEM) _ ⟨D, hD, hD2, rfl⟩
    (hE.trans inf_le_left)

theorem normalizer_le_of_four_le_pRank (hU : uniqueFourUnique G) {M : Subgroup G}
    (hM : uniqueFourIsMaxTwoLocal M) {K : Subgroup G} (hKM : K ≤ M) {q : ℕ} (hq : q.Prime)
    (hq2 : q ≠ 2) (h4 : 4 ≤ CFSG.Open.pRank q K) : Subgroup.normalizer (K : Set G) ≤ M := by
  haveI : Fact q.Prime := ⟨hq⟩
  obtain ⟨P, hPM, hΓM⟩ := CFSG.LocalAnalysis.UniquenessCase.UC6.exists_sylow_le_of_sigma hU hM
    (CFSG.LocalAnalysis.UniquenessCase.UC6.four_le_pRank_imp_mem_sigma hU hM hq hq2
      (h4.trans (CFSG.SectionRank.pRank_mono hq.one_lt hKM)))
  obtain ⟨E, hEK, hEel, hEcard⟩ := CFSG.SectionRank.exists_pRank hq.one_lt K
  obtain ⟨X, hX, hEX⟩ :=
    CFSG.LocalAnalysis.UniquenessCase.UC6.exists_isSylowOf_ge hEK hEel.isPGroup
  have hNX : Subgroup.normalizer (X : Set G) ≤ M :=
    CFSG.AGLEmbeddingD2.normalizer_le_of_core hq P hPM hΓM (hX.le.trans hKM) hX.isPGroup
      ((le_trans (by norm_num) h4).trans (CFSG.SectionRank.le_pRank hq.one_lt hEX hEel hEcard))
  intro g hg
  obtain ⟨k, hk, hkg⟩ :=
    CFSG.RankThree.PartOne.Sec15Frattini.exists_mem_normalizer_of_isSylowOf hX hg
  simpa using M.mul_mem (hKM hk) (hNX hkg)

theorem pRank_pPrimeCore_le_three_of_normalizer_le (hU : uniqueFourUnique G) {M : Subgroup G}
    (hM : uniqueFourIsMaxTwoLocal M) {p : ℕ} (hp : p.Prime) (hsp : IsStronglyPEmbedded p M)
    (huniq : ∀ D : Subgroup G, D ≠ ⊥ → IsPGroup 2 D →
      2 ≤ CFSG.Open.pRank p (Subgroup.normalizer (D : Set G) ⊓ M) →
      Subgroup.normalizer (D : Set G) ≤ M)
    {H : Subgroup G} (hHM : ¬ H ≤ M) (hHrank : 2 ≤ CFSG.Open.pRank p (H ⊓ M)) {q : ℕ}
    (hq : q.Prime) : CFSG.Open.pRank q ((CFSG.pPrimeCore p ↥H).map H.subtype) ≤ 3 := by
  by_contra hlt
  have h4 : 4 ≤ CFSG.Open.pRank q ((CFSG.pPrimeCore p ↥H).map H.subtype) := by omega
  rcases eq_or_ne q 2 with rfl | hq2
  ·
    refine (Nat.not_even_iff_odd.mpr (Section7.odd_card_pPrimeCore hsp hp huniq hHM hHrank))
      (even_iff_two_dvd.mpr ?_)
    rw [← Subgroup.card_map_of_injective H.subtype_injective]
    exact CFSG.GroupTheory.dvd_card_of_one_le_pRank Nat.prime_two (by omega)
  ·
    refine hHM (le_trans ?_ (normalizer_le_of_four_le_pRank hU hM
      (Section7.pPrimeCore_le hsp hp hHrank) hq hq2 h4))
    have h := Subgroup.le_normalizer_map (H := CFSG.pPrimeCore p ↥H) H.subtype
    rwa [Subgroup.normalizer_eq_top, Subgroup.map_top, Subgroup.range_subtype] at h

@[expose] def setup4Core (hS : Standing4 G) (hU : uniqueFourUnique G) (S : Setup4 G)
    (hPart : PartIAt S.M) (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2)
    (hsp : IsStronglyPEmbedded p S.M) : Sec7Core4 G where
  standing := ⟨hS.simple, hS.nonab, hS.kProper, hS.charTwo, le_trans (by norm_num) hS.rank⟩
  M := S.M
  maxLocal := S.maxLocal
  p := p
  prime := hp
  odd := hp2
  strong := hsp
  huniq := normalizer_le_of_theoremCAt hPart.1 hp hp2 hsp
  rankK := fun _ hHM hrank _ hq =>
    pRank_pPrimeCore_le_three_of_normalizer_le hU S.maxLocal hp hsp
      (normalizer_le_of_theoremCAt hPart.1 hp hp2 hsp) hHM hrank hq

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.R72
