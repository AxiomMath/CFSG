module

public import CFSG.LocalAnalysis.UniquenessCase.UC6S846e
public import CFSG.LocalAnalysis.UniquenessCase.UC22DataExt
public import CFSG.LocalAnalysis.RankThreeUC.StronglyEmbedded

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC6S846

open Subgroup CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.Yardstones.Mf4cdcdf2e013 (Standing4 Setup4 SigmaOne4 SigmaTwo4)
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)

variable {G : Type} [Group G] [Finite G]

theorem solvable_of_sigmaTwo4 (hU : CFSG.Open.uniqueFourUnique G) {M : Subgroup G}
    (hM : CFSG.Open.uniqueFourIsMaxTwoLocal M) {p : ℕ} (hp : p ∈ CFSG.Open.uniqueFourSigma M)
    (h2 : SigmaTwo4 G p) : Group.IsSolvable ↥M := by
  obtain ⟨-, N, hN, hpN, hcl⟩ := h2
  obtain ⟨-, -, -, -, hNsolv, -⟩ := hcl
  haveI : Fact p.Prime := ⟨hp.1.1⟩
  obtain ⟨PM, hPM, -⟩ := UC6.exists_sylow_le_of_sigma hU hM hp
  obtain ⟨PN, hPN, -⟩ := UC6.exists_sylow_le_of_sigma hU hN hpN
  obtain ⟨g, hg⟩ := UC6.exists_le_uniqueFourConj_sylow (PM.isPGroup') PN
  have hPMN : (PM : Subgroup G) ≤ CFSG.Open.uniqueFourConj g N :=
    hg.trans (UC6.uniqueFourConj_mono hPN g)
  have hN' : CFSG.Open.uniqueFourIsMaxTwoLocal (CFSG.Open.uniqueFourConj g N) :=
    UC6.isMaxTwoLocal_conj hN g
  have hpN' : p ∈ CFSG.Open.uniqueFourSigma (CFSG.Open.uniqueFourConj g N) :=
    UC6.mem_uniqueFourSigma_conj hpN g
  have h4 : 2 ≤ Open.pRank p (PM : Subgroup G) :=
    le_trans (by norm_num) (UC6.four_le_pRank_sylow hp.1 PM)
  have hle : M ≤ CFSG.Open.uniqueFourConj g N := UC6.sec61 hU hN' hpN' hPMN h4 hM.1 hPM
  have heq : CFSG.Open.uniqueFourConj g N = M := hM.2 _ hN'.1 hle
  rw [← heq]
  have hsurj : Function.Surjective
      (Subgroup.equivMapOfInjective N (MulAut.conj g⁻¹).toMonoidHom (MulAut.conj g⁻¹).injective).toMonoidHom :=
    (Subgroup.equivMapOfInjective N _ _).surjective
  haveI := hNsolv
  exact Group.isSolvable_of_surjective hsurj

theorem sigmaStd_dataOfSetup4 (hS : Standing4 G) (hU : CFSG.Open.uniqueFourUnique G) (S : Setup4 G) :
    SigmaStd (UC6.dataOfSetup4 hS hU S) where
  nonempty := ⟨S.p, S.hp⟩
  three_le := fun p hp => le_trans (by norm_num) (UC6.four_le_pRank_of_sigma hp)
  sig1_sp := fun p hp => UC6.isStronglyPEmbedded_of_sigmaOne hU S.maxLocal hp.1 hp.2
  solvable_of := by
    rintro ⟨p, hp⟩
    rcases hp with hp | hp
    · exact solvable_of_sigmaTwo4 hU S.maxLocal hp.1 hp.2
    · exact absurd hp (by simp [UC6.dataOfSetup4])
  four_mem := fun r hr hr2 h4 => UC6.four_le_pRank_imp_mem_sigma hU S.maxLocal hr hr2 h4

theorem ne_bot_of_three_le_pRank {p : ℕ} (hp : p.Prime) {Q : Subgroup G} (h : 3 ≤ Open.pRank p Q) :
    Q ≠ ⊥ := by
  rintro rfl
  obtain ⟨E, hE, -, hcard⟩ := CFSG.PreuniquenessRankFour.Helpers.pRank_attained p hp (⊥ : Subgroup G)
  rw [le_bot_iff.mp hE, Subgroup.card_bot] at hcard
  have : p ^ Open.pRank p (⊥ : Subgroup G) = 1 := hcard.symm
  have h0 : Open.pRank p (⊥ : Subgroup G) = 0 := by
    by_contra hne
    have := Nat.one_lt_pow hne hp.one_lt
    omega
  omega

theorem sigmaStd_dataOfSetup (hS : CFSG.LocalAnalysis.RankThreeUC.Standing G)
    (S : CFSG.LocalAnalysis.RankThreeUC.Setup G) :
    SigmaStd (PartTwo.Three.dataOfSetup hS S) where
  nonempty := ⟨S.p, PartTwo.Three.mem_sigmaOf S⟩
  three_le := (dataExt_ofSetup hS S).three_le
  sig1_sp := by
    rintro p ⟨hσ, Q, hw, hΓ⟩
    haveI : Fact p.Prime := ⟨CFSG.RankThreeCoreUniqueness.Helpers.sigmaA_prime p hσ⟩
    have hP3 := CFSG.RankThreeCoreUniqueness.Helpers.selected_sylow_rank_at_least_three hS.rank p hσ Q
    have hM : S.M ≠ ⊤ := by
      haveI := hS.simple
      exact CFSG.PreuniquenessRankFour.Helpers.twoLocal_ne_top hS.nonab hw.maxLocal.1
    exact (CFSG.LocalAnalysis.RankThreeUC.gamma_one_le_iff_isStronglyPEmbedded
      (hw.sylow_le hS hσ) hM (ne_bot_of_three_le_pRank (Fact.out : p.Prime) hP3)).1 hΓ
  solvable_of := by
    rintro ⟨p, hp⟩
    rcases hp with ⟨-, Q, -, hB⟩ | ⟨-, -, Q, -, hC⟩
    · exact hB.2.1
    · exact hC.1
  four_mem := by
    intro r hr hr2 h4
    exfalso
    have := CFSG.RankThreeCoreUniqueness.Helpers.local_pRank_le_evenRank r hr hr2 S.M S.witness.maxLocal.1
    rw [hS.rank] at this
    have h4' : 4 ≤ Open.pRank r S.M := h4
    omega

end CFSG.LocalAnalysis.UniquenessCase.UC6S846
