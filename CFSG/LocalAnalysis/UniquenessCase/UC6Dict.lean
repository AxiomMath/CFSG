module

public import CFSG.LocalAnalysis.UniquenessCase.UC6Basic
public import CFSG.Yardstones.Mf4cdcdf2e013.Definitions
public import CFSG.RankThree.PartOne.CTP.StrongPGlue
public import CFSG.LocalAnalysis.PreuniquenessRankFour.Helpers
public import CFSG.GroupTheory.ElementaryAbelianTransport
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection4.lemma_4_5_a
public import CFSG.LocalAnalysis.SectionRank.SubgroupRank

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC6

open Subgroup CFSG.Open
open CFSG.Yardstones.Mf4cdcdf2e013 (Standing4 Setup4 TheoremCAt SigmaOne4)
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)

variable {G : Type} [Group G] [Finite G]

theorem uniqueFourConj_conj_inv {H : Subgroup G} {g : G} :
    uniqueFourConj g (uniqueFourConj g⁻¹ H) = H := by
  ext x
  rw [mem_uniqueFourConj_iff, mem_uniqueFourConj_iff]
  simp [mul_assoc]

theorem uniqueFourConj_inv_conj {H : Subgroup G} {g : G} :
    uniqueFourConj g⁻¹ (uniqueFourConj g H) = H := by
  simpa using (uniqueFourConj_conj_inv (H := H) (g := g⁻¹))

theorem uniqueFourConj_mono {H K : Subgroup G} (h : H ≤ K) (g : G) :
    uniqueFourConj g H ≤ uniqueFourConj g K := Subgroup.map_mono h

theorem card_uniqueFourConj (H : Subgroup G) (g : G) :
    Nat.card (uniqueFourConj g H) = Nat.card H :=
  Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective

theorem uniqueFourConj_normalizer (H : Subgroup G) (g : G) :
    uniqueFourConj g (normalizer (H : Set G)) = normalizer (uniqueFourConj g H : Set G) :=
  Subgroup.map_equiv_normalizer_eq H (MulAut.conj g⁻¹)

theorem isPGroup_uniqueFourConj {p : ℕ} {H : Subgroup G} (h : IsPGroup p H) (g : G) :
    IsPGroup p (uniqueFourConj g H) := h.map _

theorem uniqueFourConj_ne_bot {H : Subgroup G} (h : H ≠ ⊥) (g : G) : uniqueFourConj g H ≠ ⊥ :=
  fun hb => h ((Subgroup.map_eq_bot_iff_of_injective _ (MulAut.conj g⁻¹).injective).1 hb)

theorem isTwoLocal_conj {H : Subgroup G} (h : IsTwoLocal H) (g : G) :
    IsTwoLocal (uniqueFourConj g H) := by
  obtain ⟨P, hP1, hP2, rfl⟩ := h
  exact ⟨uniqueFourConj g P, uniqueFourConj_ne_bot hP1 g, isPGroup_uniqueFourConj hP2 g,
    uniqueFourConj_normalizer P g⟩

theorem isMaxTwoLocal_conj {M : Subgroup G} (h : IsMaxTwoLocalSubgroup M) (g : G) :
    IsMaxTwoLocalSubgroup (uniqueFourConj g M) := by
  refine ⟨isTwoLocal_conj h.1 g, fun H hH hle => ?_⟩
  have h1 : M ≤ uniqueFourConj g⁻¹ H := by
    have := uniqueFourConj_mono hle g⁻¹
    rwa [uniqueFourConj_inv_conj] at this
  have h2 := h.2 _ (isTwoLocal_conj hH g⁻¹) h1
  rw [← h2, uniqueFourConj_conj_inv]

theorem le_pRank_of_elemAbelian {p : ℕ} (hp : p.Prime) {H E : Subgroup G} (hEH : E ≤ H)
    (hel : IsElemAbelian p E) {k : ℕ} (hcard : Nat.card E = p ^ k) : k ≤ Open.pRank p H :=
  le_csSup (CFSG.PreuniquenessRankFour.Helpers.pRank_bddAbove p hp H) ⟨E, hEH, hel, hcard⟩

theorem pRank_uniqueFourConj_le (p : ℕ) (hp : p.Prime) (H : Subgroup G) (g : G) :
    Open.pRank p H ≤ Open.pRank p (uniqueFourConj g H) := by
  obtain ⟨E, hEH, hEel, hEcard⟩ :=
    CFSG.PreuniquenessRankFour.Helpers.pRank_attained p hp H
  exact le_pRank_of_elemAbelian hp (uniqueFourConj_mono hEH g) (IsElemAbelian.map hEel (MulAut.conj g⁻¹).toMonoidHom)
    (by rw [card_uniqueFourConj, hEcard])

theorem pRank_uniqueFourConj (p : ℕ) (hp : p.Prime) (H : Subgroup G) (g : G) :
    Open.pRank p (uniqueFourConj g H) = Open.pRank p H := by
  refine le_antisymm ?_ (pRank_uniqueFourConj_le p hp H g)
  have := pRank_uniqueFourConj_le p hp (uniqueFourConj g H) g⁻¹
  rwa [uniqueFourConj_inv_conj] at this

theorem mem_uniqueFourSigma_conj {M : Subgroup G} {p : ℕ} (h : p ∈ uniqueFourSigma M) (g : G) :
    p ∈ uniqueFourSigma (uniqueFourConj g M) := by
  obtain ⟨hβ, B, hB, hBM⟩ := h
  refine ⟨hβ, uniqueFourConj g B, ?_, uniqueFourConj_mono hBM g⟩
  have hel : IsElemAbelian p B := hB.1
  have hcard : Nat.card B = p ^ uniqueFourTwoLocalRank p G := hB.2.1
  obtain ⟨U, hU1, hU2, hBU⟩ := hB.2.2
  refine ⟨IsElemAbelian.map hel (MulAut.conj g⁻¹).toMonoidHom, ?_, uniqueFourConj g U, uniqueFourConj_ne_bot hU1 g,
    isPGroup_uniqueFourConj hU2 g, ?_⟩
  · rw [card_uniqueFourConj]
    exact hcard
  · rw [← uniqueFourConj_normalizer]
    exact uniqueFourConj_mono hBU g

theorem isStronglyPEmbedded_uniqueFourConj {p : ℕ} {M : Subgroup G} (h : IsStronglyPEmbedded p M)
    (g : G) : IsStronglyPEmbedded p (uniqueFourConj g M) :=
  CFSG.RankThree.PartOne.IsStronglyPEmbedded.conj h g⁻¹

theorem exists_le_uniqueFourConj_sylow {p : ℕ} [Fact p.Prime] {E : Subgroup G} (hE : IsPGroup p E)
    (P : Sylow p G) : ∃ g : G, E ≤ uniqueFourConj g (P : Subgroup G) := by
  obtain ⟨Q, hEQ⟩ := hE.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G P Q
  refine ⟨g⁻¹, ?_⟩
  have hQ : (Q : Subgroup G) = (P : Subgroup G).map (MulAut.conj g).toMonoidHom := by
    rw [← hg]
    exact CFSG.RankThreeCoreUniqueness.Helpers.sylow_conjugate_eq_map p P g
  unfold uniqueFourConj
  rw [inv_inv, ← hQ]
  exact hEQ

theorem pRank_sylow_eq_top {p : ℕ} [Fact p.Prime] (P : Sylow p G) :
    Open.pRank p (P : Subgroup G) = Open.pRank p (⊤ : Subgroup G) := by
  refine le_antisymm (CFSG.PreuniquenessRankFour.Helpers.pRank_mono p Fact.out le_top) ?_
  obtain ⟨E, -, hEel, hEcard⟩ :=
    CFSG.PreuniquenessRankFour.Helpers.pRank_attained p Fact.out (⊤ : Subgroup G)
  obtain ⟨g, hg⟩ := exists_le_uniqueFourConj_sylow (IsElemAbelian.isPGroup hEel) P
  have h1 := le_pRank_of_elemAbelian Fact.out hg hEel hEcard
  rwa [pRank_uniqueFourConj p Fact.out] at h1

theorem exists_maxLocal_mem_sigma {p : ℕ} (hp : p ∈ uniqueFourBeta G) :
    ∃ M : Subgroup G, uniqueFourIsMaxTwoLocal M ∧ p ∈ uniqueFourSigma M := by
  obtain ⟨B, hB⟩ := CFSG.PreuniquenessRankFour.Helpers.betaFour_has_bmax (G := G) hp
  obtain ⟨U, hU1, hU2, hBU⟩ := hB.2.2
  obtain ⟨M, hNM, hM⟩ := CFSG.PreuniquenessRankFour.Helpers.exists_maximal_twoLocal (G := G)
    (H := Subgroup.normalizer (U : Set G)) ⟨U, hU1, hU2, rfl⟩
  exact ⟨M, hM, hp, B, hB, hBU.trans hNM⟩

theorem sec61 (hU : uniqueFourUnique G) {N : Subgroup G} (hN : uniqueFourIsMaxTwoLocal N) {p : ℕ}
    (hp : p ∈ uniqueFourSigma N) {X : Subgroup G} (hXN : X ≤ N) (hX2 : 2 ≤ Open.pRank p X)
    {H : Subgroup G} (hH : IsTwoLocal H) (hXH : X ≤ H) : H ≤ N :=
  (hU N hN ⟨p, hp⟩).2 H hH ⟨p, hp, hX2.trans
    (CFSG.PreuniquenessRankFour.Helpers.pRank_mono p hp.1.1 (le_inf hXH hXN))⟩

theorem exists_sylow_le_of_sigma (hU : uniqueFourUnique G) {N : Subgroup G}
    (hN : uniqueFourIsMaxTwoLocal N) {p : ℕ} (hp : p ∈ uniqueFourSigma N) :
    ∃ P : Sylow p G, (P : Subgroup G) ≤ N ∧ uniqueFourGamma p (P : Subgroup G) ≤ N := by
  obtain ⟨_, _, _, P, hPN, hΓ, _⟩ := (hU N hN ⟨p, hp⟩).1 p hp
  exact ⟨P, hPN, hΓ⟩

theorem four_le_pRank_of_sigma {N : Subgroup G} {p : ℕ} (hp : p ∈ uniqueFourSigma N) :
    4 ≤ Open.pRank p N := by
  obtain ⟨hβ, B, hB, hBN⟩ := hp
  have h4 : 4 ≤ uniqueFourTwoLocalRank p G := hβ.2.2.2
  exact h4.trans ((CFSG.PreuniquenessRankFour.Helpers.bmax_rank_lowerBound hβ.1 hB).trans
    (CFSG.PreuniquenessRankFour.Helpers.pRank_mono p hβ.1 hBN))

theorem four_le_pRank_sylow {p : ℕ} (hp : p ∈ uniqueFourBeta G) (P : Sylow p G) :
    4 ≤ Open.pRank p (P : Subgroup G) := by
  haveI : Fact p.Prime := ⟨hp.1⟩
  rw [pRank_sylow_eq_top]
  exact CFSG.PreuniquenessRankFour.Helpers.betaFour_globalRank hp

theorem isStronglyPEmbedded_of_sigmaOne (hU : uniqueFourUnique G) {M : Subgroup G}
    (hM : uniqueFourIsMaxTwoLocal M) {p : ℕ} (hp : p ∈ uniqueFourSigma M)
    (h1 : p ∈ SigmaOne4 G) : IsStronglyPEmbedded p M := by
  obtain ⟨-, N, hN, hpN, hNs⟩ := h1
  haveI : Fact p.Prime := ⟨hp.1.1⟩
  obtain ⟨PM, hPM, -⟩ := exists_sylow_le_of_sigma hU hM hp
  obtain ⟨PN, hPN, -⟩ := exists_sylow_le_of_sigma hU hN hpN
  obtain ⟨g, hg⟩ := exists_le_uniqueFourConj_sylow (PM.isPGroup') PN
  have hPMN : (PM : Subgroup G) ≤ uniqueFourConj g N :=
    hg.trans (uniqueFourConj_mono hPN g)
  have hN' : uniqueFourIsMaxTwoLocal (uniqueFourConj g N) := isMaxTwoLocal_conj hN g
  have hpN' : p ∈ uniqueFourSigma (uniqueFourConj g N) := mem_uniqueFourSigma_conj hpN g
  have h4 : 2 ≤ Open.pRank p (PM : Subgroup G) :=
    le_trans (by norm_num) (four_le_pRank_sylow hp.1 PM)
  have hle : M ≤ uniqueFourConj g N :=
    sec61 hU hN' hpN' hPMN h4 hM.1 hPM
  have heq : uniqueFourConj g N = M := hM.2 _ hN'.1 hle
  rw [← heq]
  exact isStronglyPEmbedded_uniqueFourConj hNs g

theorem four_le_pRank_imp_mem_sigma (hU : uniqueFourUnique G) {M : Subgroup G}
    (hM : uniqueFourIsMaxTwoLocal M) {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2)
    (h4 : 4 ≤ Open.pRank r M) : r ∈ uniqueFourSigma M := by
  haveI : Fact r.Prime := ⟨hr⟩
  have hdvd : r ∣ Nat.card G :=
    CFSG.PreuniquenessRankFour.Helpers.prime_dvd_card_of_positive_rank r hr M (by omega)
  have hrank : 4 ≤ uniqueFourTwoLocalRank r G :=
    h4.trans (le_csSup (CFSG.PreuniquenessRankFour.Helpers.twoLocalRank_bddAbove r hr)
      ⟨M, hM.1, rfl⟩)
  have hβ : r ∈ uniqueFourBeta G := ⟨hr, hr2, hdvd, hrank⟩
  obtain ⟨N, hN, hrN⟩ := exists_maxLocal_mem_sigma hβ
  obtain ⟨PN, hPN, -⟩ := exists_sylow_le_of_sigma hU hN hrN
  obtain ⟨E, hEM, hEel, hEcard⟩ :=
    CFSG.PreuniquenessRankFour.Helpers.pRank_attained r hr M
  obtain ⟨g, hg⟩ := exists_le_uniqueFourConj_sylow (IsElemAbelian.isPGroup hEel) PN
  have hEN : E ≤ uniqueFourConj g N := hg.trans (uniqueFourConj_mono hPN g)
  have hN' : uniqueFourIsMaxTwoLocal (uniqueFourConj g N) := isMaxTwoLocal_conj hN g
  have hrN' : r ∈ uniqueFourSigma (uniqueFourConj g N) := mem_uniqueFourSigma_conj hrN g
  have hE2 : 2 ≤ Open.pRank r E := by
    have := le_pRank_of_elemAbelian hr le_rfl hEel hEcard
    omega
  have hle : M ≤ uniqueFourConj g N := sec61 hU hN' hrN' hEN hE2 hM.1 hEM
  have heq : uniqueFourConj g N = M := hM.2 _ hN'.1 hle
  rw [← heq]
  exact hrN'

theorem pRank_le_three_of_not_mem_sigma (hU : uniqueFourUnique G) {M : Subgroup G}
    (hM : uniqueFourIsMaxTwoLocal M) {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2)
    (hrσ : r ∉ uniqueFourSigma M) : Open.pRank r M ≤ 3 := by
  by_contra h
  exact hrσ (four_le_pRank_imp_mem_sigma hU hM hr hr2 (by omega))

theorem groupPRank_eq_pRank (p : ℕ) (E : Subgroup G) :
    CFSG.pRank p E = Open.pRank p E := by
  rw [CFSG.SectionRank.pRank_eq_open_pRank_top, ← CFSG.SectionRank.pRank_eq_pRank_top_subgroup]

theorem two_le_pRank_of_not_isCyclic {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {X : Subgroup G}
    (hX : IsPGroup p X) (hnc : ¬ IsCyclic X) : 2 ≤ Open.pRank p X := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Fact (IsPGroup p X) := ⟨hX⟩
  obtain ⟨S, -, hScard, hSel⟩ := CFSG.lemma_4_5_a hp2 hnc
  haveI := hSel
  have hSm : CFSG.IsElementaryAbelian p (S.map X.subtype) :=
    CFSG.IsElementaryAbelian.map_subtype
  have hcard : Nat.card (S.map X.subtype) = p ^ 2 := by
    rw [← hScard]
    exact (Nat.card_congr (S.equivMapOfInjective X.subtype X.subtype_injective).toEquiv).symm
  exact le_pRank_of_elemAbelian hp (Subgroup.map_subtype_le S)
    ((CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian p _).mp hSm) hcard

end CFSG.LocalAnalysis.UniquenessCase.UC6
