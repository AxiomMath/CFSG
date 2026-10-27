module

public import CFSG.LocalAnalysis.UniquenessCase.UC6Inst
public import CFSG.LocalAnalysis.UniquenessCase.UC6Syl
public import CFSG.LocalAnalysis.RankThreeCoreUniqueness.MaximalPairGeometry

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC6

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.Yardstones.Mf4cdcdf2e013 (Standing4 Setup4 TheoremCAt SigmaOne4)
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)

variable {G : Type} [Group G] [Finite G]

theorem isElemAbelian_uniqueFourConj {p : ℕ} {E : Subgroup G} (h : IsElemAbelian p E) (g : G) :
    IsElemAbelian p (uniqueFourConj g E) :=
  IsElemAbelian.map h _

theorem exists_isSylowOf_top_le {p : ℕ} [Fact p.Prime] (hU : uniqueFourUnique G) {M : Subgroup G}
    (hM : uniqueFourIsMaxTwoLocal M)
    (hpM : IsStronglyPEmbedded p M ∨ p ∈ uniqueFourSigma M) :
    ∃ P : Subgroup G, IsSylowOf p P ⊤ ∧ P ≤ M := by
  rcases hpM with hstr | hσ
  · obtain ⟨P₀, hP₀⟩ := exists_isSylowOf p M
    have hP₀1 : P₀ ≠ ⊥ := by
      intro h
      have h1 : Nat.card P₀ = 1 := by rw [h]; exact Subgroup.card_bot
      have h2 := hP₀.card_eq
      rw [h1] at h2
      have hdvd : p ∣ Nat.card M := hstr.2.1
      have hpos : 0 < (Nat.card M).factorization p :=
        (Nat.Prime.factorization_pos_of_dvd Fact.out Nat.card_pos.ne' hdvd)
      have : p ^ (Nat.card M).factorization p ≠ 1 := by
        intro h3
        exact (Nat.pos_iff_ne_zero.1 hpos) ((Nat.pow_eq_one.1 h3).resolve_left (Fact.out : p.Prime).ne_one)
      exact this h2.symm
    obtain ⟨P, hP, hP₀P⟩ := exists_isSylowOf_ge (K := ⊤) (le_top : P₀ ≤ ⊤) hP₀.isPGroup
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
  · obtain ⟨P, hPM, -⟩ := exists_sylow_le_of_sigma hU hM hσ
    refine ⟨(P : Subgroup G), ?_, hPM⟩
    rw [isSylowOf_iff]
    exact ⟨le_top, P.isPGroup', by simpa using P.not_dvd_index⟩

theorem exists_conj_eq_of_pRank_two (hU : uniqueFourUnique G) {M : Subgroup G}
    (hM : uniqueFourIsMaxTwoLocal M) (hC : TheoremCAt M) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hpM : IsStronglyPEmbedded p M ∨ p ∈ uniqueFourSigma M) {N : Subgroup G}
    (hN : uniqueFourIsMaxTwoLocal N) (hNp : 2 ≤ Open.pRank p N) :
    ∃ g : G, uniqueFourConj g M = N := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨E, hEN, hEel, hEcard⟩ := CFSG.PreuniquenessRankFour.Helpers.pRank_attained p hp N
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
  have hE'2 : 2 ≤ Open.pRank p E' := le_pRank_of_elemAbelian hp le_rfl hE'el hE'card
  obtain ⟨P₀, hP₀, hP₀M⟩ := exists_isSylowOf_top_le hU hM hpM
  obtain ⟨k, -, hk⟩ := exists_conj_le_of_isSylowOf hP₀ (le_top : E' ≤ ⊤) hE'p
  have hX : uniqueFourConj k E' ≤ M := fun x hx => by
    have hy : k * x * k⁻¹ ∈ E' := mem_uniqueFourConj_iff.1 hx
    have := hP₀M (hk _ hy)
    simpa [mul_assoc] using this
  have hXrank : 2 ≤ Open.pRank p (uniqueFourConj k E') := by
    rw [pRank_uniqueFourConj p hp]; exact hE'2
  have hN' : uniqueFourIsMaxTwoLocal (uniqueFourConj k N) := isMaxTwoLocal_conj hN k
  have hXN' : uniqueFourConj k E' ≤ uniqueFourConj k N := uniqueFourConj_mono hE'N k
  have hle : uniqueFourConj k N ≤ M := by
    rcases hpM with hstr | hσ
    · have hXel := isElemAbelian_uniqueFourConj hE'el k
      have hXcard : Nat.card (uniqueFourConj k E') = p ^ 2 := by
        rw [card_uniqueFourConj]; exact hE'card
      have hΓ : rankThreeGamma 1 p (uniqueFourConj k E') ≤ M := by
        rw [CFSG.RankThreeCoreUniqueness.Helpers.gamma_le_iff]
        intro Y hYX hY1
        have hYp : IsPGroup p Y := (IsElemAbelian.isPGroup hXel).to_le hYX
        have hY0 : Y ≠ ⊥ := by
          rintro rfl
          obtain ⟨E₀, hE₀, -, hE₀card⟩ := CFSG.PreuniquenessRankFour.Helpers.pRank_attained p hp
            (⊥ : Subgroup G)
          have h1 : E₀ = ⊥ := le_bot_iff.1 hE₀
          rw [h1, Subgroup.card_bot] at hE₀card
          have := (Nat.pow_eq_one.1 hE₀card.symm).resolve_left hp.ne_one
          omega
        exact hstr.normalizer_le hY0 hYp (hYX.trans hX)
      exact hC p hp hp2 (uniqueFourConj k E') hX (IsElemAbelian.isPGroup hXel) hXrank hΓ _ hN'.1 hXN'
    · exact sec61 hU hM hσ hX hXrank hN'.1 hXN'
  have hMN : M = uniqueFourConj k N := hN'.2 M hM.1 hle
  refine ⟨k⁻¹, ?_⟩
  rw [hMN]
  exact uniqueFourConj_inv_conj

theorem six6_one (hU : uniqueFourUnique G) {S : Setup4 G} (hC : TheoremCAt S.M) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hpM : IsStronglyPEmbedded p S.M ∨ p ∈ uniqueFourSigma S.M)
    {N : Subgroup G} (hN : uniqueFourIsMaxTwoLocal N) (hTN : S.T ≤ N)
    (hNp : 2 ≤ Open.pRank p N) : N = S.M := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨g, hg⟩ := exists_conj_eq_of_pRank_two hU S.maxLocal hC hp hp2 hpM hN hNp
  have hTU : InU S.M S.T :=
    inU_of_isSylowOf (p := 2) (normalizer_eq_of_isMaxTwoLocal S.maxLocal) S.sylowM S.normalizer_le
  rw [← hg] at hTN
  rw [← hg]
  exact hTU.2 g hTN

theorem six6_two (hU : uniqueFourUnique G) {M : Subgroup G} (hM : uniqueFourIsMaxTwoLocal M)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {N : Subgroup G} (hN : uniqueFourIsMaxTwoLocal N)
    (h4 : 4 ≤ Open.pRank p N) (h2 : 2 ≤ Open.pRank p (M ⊓ N)) : N = M := by
  have hσ : p ∈ uniqueFourSigma N := four_le_pRank_imp_mem_sigma hU hN hp hp2 h4
  obtain ⟨E, hE, hEel, hEcard⟩ := CFSG.PreuniquenessRankFour.Helpers.pRank_attained p hp (M ⊓ N)
  have hE2 : 2 ≤ Open.pRank p E :=
    h2.trans (le_pRank_of_elemAbelian hp le_rfl hEel hEcard)
  have hle : M ≤ N := sec61 hU hN hσ (hE.trans inf_le_right) hE2 hM.1 (hE.trans inf_le_left)
  exact hM.2 N hN.1 hle

theorem r6_6_dataOfSetup4 (hS : Standing4 G) (hU : uniqueFourUnique G) (S : Setup4 G)
    (hMS : S.InMSigma) (hC : TheoremCAt S.M) : R6_6 (dataOfSetup4 hS hU S) := by
  intro p hp hp2
  have h1 : (IsStronglyPEmbedded p S.M ∨ p ∈ uniqueFourSigma S.M) →
      ∀ N ∈ calMOf S.T, 2 ≤ Open.pRank p N → N = S.M := fun hpM N hN hNp =>
    six6_one hU hC hp hp2 hpM hN.1 hN.2 hNp
  refine ⟨h1, fun N hN h4 h2 => six6_two hU S.maxLocal hp hp2 hN h4 h2, ?_⟩
  rintro rfl N hN h4
  by_cases h3β : 3 ∈ uniqueFourBeta G
  · have hS3 : S.p = 3 := hMS.1 h3β
    have hσ3 : 3 ∈ uniqueFourSigma S.M := hS3 ▸ S.hp
    exact h1 (Or.inr hσ3) N hN (by omega)
  · exfalso
    exact h3β (four_le_pRank_imp_mem_sigma hU hN.1 Nat.prime_three (by norm_num) h4).1

end CFSG.LocalAnalysis.UniquenessCase.UC6
