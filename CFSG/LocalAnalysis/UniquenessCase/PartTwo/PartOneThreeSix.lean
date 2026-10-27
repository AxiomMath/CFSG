module

import CFSG.LocalAnalysis.UniquenessCase.UC6Dict
import CFSG.LocalAnalysis.UniquenessCase.UC6Syl
import CFSG.LocalAnalysis.RankThreeCoreUniqueness.MaximalPairGeometry
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.DataThree
public import CFSG.LocalAnalysis.UniquenessCase.UC6R

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Three

open Subgroup CFSG.Open CFSG.LocalAnalysis.RankThreeUC CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

private theorem exists_isSylowOf_top_le_three {p : ℕ} [Fact p.Prime] (hS : Standing G)
    {M : Subgroup G} (hM : rankThreeIsMaxTwoLocal M)
    (hpM : CFSG.RankThree.PartOne.IsStronglyPEmbedded p M ∨ p ∈ sigmaOf M) :
    ∃ P : Subgroup G, CFSG.ABGLocalTools.IsSylowOf p P ⊤ ∧ P ≤ M := by
  rcases hpM with hstr | hσ
  · obtain ⟨P₀, hP₀⟩ := CFSG.ABGLocalTools.exists_isSylowOf p M
    have hP₀1 : P₀ ≠ ⊥ := by
      intro h
      have h1 : Nat.card P₀ = 1 := by rw [h]; exact Subgroup.card_bot
      have h2 := hP₀.card_eq
      rw [h1] at h2
      have hdvd : p ∣ Nat.card M := hstr.2.1
      have hpos : 0 < (Nat.card M).factorization p :=
        Nat.Prime.factorization_pos_of_dvd Fact.out Nat.card_pos.ne' hdvd
      have : p ^ (Nat.card M).factorization p ≠ 1 := by
        intro h3
        exact (Nat.pos_iff_ne_zero.1 hpos)
          ((Nat.pow_eq_one.1 h3).resolve_left (Fact.out : p.Prime).ne_one)
      exact this h2.symm
    obtain ⟨P, hP, hP₀P⟩ := UC6.exists_isSylowOf_ge (K := ⊤) (le_top : P₀ ≤ ⊤) hP₀.isPGroup
    refine ⟨P, hP, ?_⟩
    by_cases heq : P₀ = P
    · rw [← heq]; exact hP₀.le
    · exfalso
      have hlt : P₀ < P := lt_of_le_of_ne hP₀P heq
      have hgrow := CFSG.RankThreeCoreUniqueness.Helpers.pGroup_proper_subgroup_lt_internal_normalizer
        p Fact.out P P₀ hP.isPGroup hlt
      have hNM : P ⊓ normalizer (P₀ : Set G) ≤ M := fun x hx =>
        hstr.normalizer_le hP₀1 hP₀.isPGroup hP₀.le hx.2
      have := hP₀.eq_of_le hgrow.le hNM hP.isPGroup.to_inf_left
      exact hgrow.ne this.symm
  · obtain ⟨hpA, Q, hw⟩ := hσ
    refine ⟨(Q : Subgroup G), ?_, hw.sylow_le hS hpA⟩
    rw [CFSG.ABGLocalTools.isSylowOf_iff]
    exact ⟨le_top, Q.isPGroup', by simpa using Q.not_dvd_index⟩

private theorem exists_conj_eq_of_pRank_two_three (hS : Standing G) {M : Subgroup G}
    (hM : rankThreeIsMaxTwoLocal M) (hC : CFSG.Yardstones.Mf4cdcdf2e013.TheoremCAt M) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2)
    (hpM : CFSG.RankThree.PartOne.IsStronglyPEmbedded p M ∨ p ∈ sigmaOf M) {N : Subgroup G}
    (hN : rankThreeIsMaxTwoLocal N) (hNp : 2 ≤ CFSG.Open.pRank p N) :
    ∃ g : G, uniqueFourConj g M = N := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨E, hEN, hEel, hEcard⟩ :=
    CFSG.RankThreeCoreUniqueness.Helpers.pRank_attained p N (by omega)
  have hdvd : p ^ 2 ∣ Nat.card E := by rw [hEcard]; exact pow_dvd_pow p hNp
  obtain ⟨K, hKcard, -⟩ := Sylow.exists_subgroup_card_pow_prime_le (G := ↥E) p (n := 0) (m := 2)
    hdvd ⊥ (by simp) (by norm_num)
  set E' : Subgroup G := K.map E.subtype with hE'
  have hE'E : E' ≤ E := Subgroup.map_subtype_le K
  have hE'N : E' ≤ N := hE'E.trans hEN
  have hE'el : IsElemAbelian p E' := hEel.mono hE'E
  have hE'card : Nat.card E' = p ^ 2 := by
    rw [hE', Subgroup.card_map_of_injective E.subtype_injective]; exact hKcard
  have hE'p : IsPGroup p E' := IsElemAbelian.isPGroup hE'el
  have hE'2 : 2 ≤ CFSG.Open.pRank p E' :=
    le_csSup (CFSG.RankThreeCoreUniqueness.Helpers.pRank_set_bddAbove p hp.one_lt E')
      ⟨E', le_rfl, hE'el, hE'card⟩
  obtain ⟨P₀, hP₀, hP₀M⟩ := exists_isSylowOf_top_le_three hS hM hpM
  obtain ⟨k, -, hk⟩ := UC6.exists_conj_le_of_isSylowOf hP₀ (le_top : E' ≤ ⊤) hE'p
  have hX : uniqueFourConj k E' ≤ M := fun x hx => by
    have hy : k * x * k⁻¹ ∈ E' := UC6.mem_uniqueFourConj_iff.1 hx
    have := hP₀M (hk _ hy)
    simpa [mul_assoc] using this
  have hXrank : 2 ≤ CFSG.Open.pRank p (uniqueFourConj k E') := by
    rw [UC6.pRank_uniqueFourConj p hp]; exact hE'2
  have hN' : rankThreeIsMaxTwoLocal (uniqueFourConj k N) := UC6.isMaxTwoLocal_conj hN k
  have hXN' : uniqueFourConj k E' ≤ uniqueFourConj k N := UC6.uniqueFourConj_mono hE'N k
  have hle : uniqueFourConj k N ≤ M := by
    rcases hpM with hstr | hσ
    · have hXel : IsElemAbelian p (uniqueFourConj k E') :=
        IsElemAbelian.map hE'el (MulAut.conj k⁻¹).toMonoidHom
      have hXcard : Nat.card (uniqueFourConj k E') = p ^ 2 := by
        rw [UC6.card_uniqueFourConj]; exact hE'card
      have hΓ : rankThreeGamma 1 p (uniqueFourConj k E') ≤ M := by
        rw [CFSG.RankThreeCoreUniqueness.Helpers.gamma_le_iff]
        intro Y hYX hY1
        have hYp : IsPGroup p Y := (IsElemAbelian.isPGroup hXel).to_le hYX
        have hY0 : Y ≠ ⊥ := by
          rintro rfl
          obtain ⟨E₀, hE₀, -, hE₀card⟩ :=
            CFSG.PreuniquenessRankFour.Helpers.pRank_attained p hp (⊥ : Subgroup G)
          have h1 : E₀ = ⊥ := le_bot_iff.1 hE₀
          rw [h1, Subgroup.card_bot] at hE₀card
          have := (Nat.pow_eq_one.1 hE₀card.symm).resolve_left hp.ne_one
          omega
        exact hstr.normalizer_le hY0 hYp (hYX.trans hX)
      exact hC p hp hp2 (uniqueFourConj k E') hX (IsElemAbelian.isPGroup hXel) hXrank hΓ _
        hN'.1 hXN'
    · obtain ⟨hpA, Q, hw⟩ := hσ
      exact hw.le_of_le_of_two_le_pRank hpA hX hXrank hN'.1 hXN'
  have hMN : M = uniqueFourConj k N := hN'.2 M hM.1 hle
  refine ⟨k⁻¹, ?_⟩
  rw [hMN]
  exact UC6.uniqueFourConj_inv_conj

theorem r6_6_dataOfSetup (hS : Standing G) (hUC : rankThreeUC G) (hC : AGL81TheoremC G)
    (S : Setup G) : UC6.R6_6 (dataOfSetup hS S) := by
  intro p hp hp2
  haveI : Fact p.Prime := ⟨hp⟩
  refine ⟨?_, ?_, ?_⟩
  · intro hpM N hN hNp
    obtain ⟨hNmax, hTN⟩ := hN
    obtain ⟨g, hg⟩ := exists_conj_eq_of_pRank_two_three hS S.witness.maxLocal
      (hC hUC S.p S.hp S.P S.M S.witness) hp hp2 hpM hNmax hNp
    have hTU : UC6.InU S.M S.T :=
      UC6.inU_of_isSylowOf (p := 2) (UC6.normalizer_eq_of_isMaxTwoLocal S.witness.maxLocal)
        S.sylowM S.normalizer_le
    rw [← hg] at hTN
    rw [← hg]
    exact hTU.2 g hTN
  · intro N hN h4 _
    have := CFSG.RankThreeCoreUniqueness.Helpers.local_pRank_le_evenRank p hp hp2 N hN.1
    rw [hS.rank] at this
    omega
  · intro _ N hN h4
    have := CFSG.RankThreeCoreUniqueness.Helpers.local_pRank_le_evenRank 3
      Nat.prime_three (by norm_num) N hN.1.1
    rw [hS.rank] at this
    omega

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Three
