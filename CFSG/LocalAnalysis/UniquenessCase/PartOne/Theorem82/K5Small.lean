module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.KInputs811
public import CFSG.LocalAnalysis.SectionRank.AmbientRank
public import CFSG.HardMathSupport.Timmesfeld.Tables.Alt.Rank
public import CFSG.HardMathSupport.Timmesfeld.DefChar.CoreA
public import CFSG.GH74.Generic.Context
public import CFSG.GH74.KGroups.PSL2
public import CFSG.LocalAnalysis.AGLEmbedding.LinTwoAutCard
public import CFSG.Quasithin.Background.SimsF5Omega5

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82

open CFSG.Open Subgroup
open CFSG.Blueprint (LieModel)
open CFSG.ComponentClassification.OuterAutomorphisms
open CFSG.LocalAnalysis.UniquenessCase.UC22

theorem card_PSp43 : Nat.card CFSG.GH74.Exceptional.PSp43 = 25920 := by
  rw [Nat.card_congr CFSG.GH74.Exceptional.psp43EquivU2.toEquiv]
  exact CFSG.GH74.Exceptional.card_U2_four

theorem psp43_equiv_of_lieModel {S : Type} [Group S] (h : LieModel S .PSp 2 3 1) :
    Nonempty (S ≃* CFSG.GH74.Exceptional.PSp43) := by
  obtain ⟨-, -, F, _, _, hF, ⟨e⟩⟩ := CFSG.GH74.Generic.lieModel_psp_data h
  haveI : Fintype F := Fintype.ofFinite F
  have hc : Fintype.card F = Fintype.card (ZMod 3) := by
    rw [← Nat.card_eq_fintype_card, hF, ZMod.card]
    norm_num
  let φ : F ≃+* ZMod 3 := FiniteField.ringEquivOfCardEq hc
  refine ⟨e.trans (CFSG.Adapters.RankTwoModelTransports.statedProjCongr
    (CFSG.Adapters.RankTwoModelTransports.glCongr φ)
    (CFSG.Adapters.RankTwoModelTransports.glCongr_statedSp φ 2)
    (CFSG.Adapters.RankTwoModelTransports.glCongr_statedScalars φ))⟩

theorem center_PSp43_eq_bot : Subgroup.center CFSG.GH74.Exceptional.PSp43 = ⊥ := by
  have hsimple : IsSimpleGroup CFSG.GH74.Exceptional.PSp43 :=
    CFSG.ClassicalGroups.Symplectic.isSimpleGroup_statedProj_statedSp (ZMod 3) 2 (by norm_num)
      (Or.inr (Or.inl ⟨by rw [Nat.card_eq_fintype_card, ZMod.card], le_rfl⟩))
  haveI : IsSimpleGroup CFSG.GH74.Exceptional.PSp43 := hsimple
  refine CFSG.HardMathSupport.Timmesfeld.DefChar.center_eq_bot_of_simple hsimple ?_
  by_contra hc
  push Not at hc
  haveI : IsMulCommutative CFSG.GH74.Exceptional.PSp43 := ⟨⟨fun a b => hc a b⟩⟩
  have hp := (Group.is_simple_iff_prime_card (α := CFSG.GH74.Exceptional.PSp43)).1 hsimple
  rw [card_PSp43] at hp
  norm_num at hp

theorem dvd_25920_mulAut_PSp43 :
    25920 ∣ Nat.card (MulAut CFSG.GH74.Exceptional.PSp43) := by
  have hconj : Function.Injective (MulAut.conj : CFSG.GH74.Exceptional.PSp43 →*
      MulAut CFSG.GH74.Exceptional.PSp43) :=
    CFSG.HardMathSupport.Timmesfeld.DefChar.conj_injective_of_center_eq_bot center_PSp43_eq_bot
  have hinner : Nat.card ↥(MulAut.conj : CFSG.GH74.Exceptional.PSp43 →*
      MulAut CFSG.GH74.Exceptional.PSp43).range = 25920 := by
    rw [← Nat.card_congr (MonoidHom.ofInjective hconj).toEquiv]
    exact card_PSp43
  rw [← hinner]
  exact Subgroup.card_subgroup_dvd_card _

theorem not_sq_dvd_25920 {p : ℕ} (hp : p.Prime) (h5 : 5 ≤ p) : ¬ p ^ 2 ∣ 25920 := by
  intro h
  have hmem : p ∈ (25920 : ℕ).primeFactors :=
    Nat.mem_primeFactors.2 ⟨hp, (dvd_pow_self p (by norm_num)).trans h, by norm_num⟩
  rw [show (25920 : ℕ).primeFactors = {2, 3, 5} by norm_num [Nat.primeFactors]] at hmem
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
  rcases hmem with rfl | rfl | rfl
  · omega
  · omega
  · norm_num at h

theorem not_sq_dvd_51840 {p : ℕ} (hp : p.Prime) (h5 : 5 ≤ p) : ¬ p ^ 2 ∣ 51840 := by
  intro h
  have hmem : p ∈ (51840 : ℕ).primeFactors :=
    Nat.mem_primeFactors.2 ⟨hp, (dvd_pow_self p (by norm_num)).trans h, by norm_num⟩
  rw [show (51840 : ℕ).primeFactors = {2, 3, 5} by norm_num [Nat.primeFactors]] at hmem
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
  rcases hmem with rfl | rfl | rfl
  · omega
  · omega
  · norm_num at h

theorem not_sq_dvd_58968 {p : ℕ} (hp : p.Prime) (h5 : 5 ≤ p) : ¬ p ^ 2 ∣ 58968 := by
  intro h
  have hmem : p ∈ (58968 : ℕ).primeFactors :=
    Nat.mem_primeFactors.2 ⟨hp, (dvd_pow_self p (by norm_num)).trans h, by norm_num⟩
  rw [show (58968 : ℕ).primeFactors = {2, 3, 7, 13} by norm_num [Nat.primeFactors]] at hmem
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
  rcases hmem with rfl | rfl | rfl | rfl
  · omega
  · omega
  · norm_num at h
  · norm_num at h

theorem not_sq_dvd_50232960 {p : ℕ} (hp : p.Prime) (h5 : 5 ≤ p) :
    ¬ p ^ 2 ∣ 50232960 := by
  intro h
  have hmem : p ∈ (50232960 : ℕ).primeFactors :=
    Nat.mem_primeFactors.2 ⟨hp, (dvd_pow_self p (by norm_num)).trans h, by norm_num⟩
  rw [show (50232960 : ℕ).primeFactors = {2, 3, 5, 17, 19} by norm_num [Nat.primeFactors]]
    at hmem
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl
  · omega
  · omega
  · norm_num at h
  · norm_num at h
  · norm_num at h

theorem not_sq_dvd_100465920 {p : ℕ} (hp : p.Prime) (h5 : 5 ≤ p) :
    ¬ p ^ 2 ∣ 100465920 := by
  intro h
  have hmem : p ∈ (100465920 : ℕ).primeFactors :=
    Nat.mem_primeFactors.2 ⟨hp, (dvd_pow_self p (by norm_num)).trans h, by norm_num⟩
  rw [show (100465920 : ℕ).primeFactors = {2, 3, 5, 17, 19} by norm_num [Nat.primeFactors]]
    at hmem
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl
  · omega
  · omega
  · norm_num at h
  · norm_num at h
  · norm_num at h

theorem not_sq_dvd_460815505920 {p : ℕ} (hp : p.Prime) (h5 : 5 ≤ p) (hp7 : p ≠ 7) :
    ¬ p ^ 2 ∣ 460815505920 := by
  intro h
  have hmem : p ∈ (460815505920 : ℕ).primeFactors :=
    Nat.mem_primeFactors.2 ⟨hp, (dvd_pow_self p (by norm_num)).trans h, by norm_num⟩
  rw [show (460815505920 : ℕ).primeFactors = {2, 3, 5, 7, 11, 19, 31} by
    norm_num [Nat.primeFactors]] at hmem
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · omega
  · omega
  · norm_num at h
  · exact absurd rfl hp7
  · norm_num at h
  · norm_num at h
  · norm_num at h

theorem not_sq_dvd_921631011840 {p : ℕ} (hp : p.Prime) (h5 : 5 ≤ p) (hp7 : p ≠ 7) :
    ¬ p ^ 2 ∣ 921631011840 := by
  intro h
  have hmem : p ∈ (921631011840 : ℕ).primeFactors :=
    Nat.mem_primeFactors.2 ⟨hp, (dvd_pow_self p (by norm_num)).trans h, by norm_num⟩
  rw [show (921631011840 : ℕ).primeFactors = {2, 3, 5, 7, 11, 19, 31} by
    norm_num [Nat.primeFactors]] at hmem
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · omega
  · omega
  · norm_num at h
  · exact absurd rfl hp7
  · norm_num at h
  · norm_num at h
  · norm_num at h

theorem not_sq_dvd_1843262023680 {p : ℕ} (hp : p.Prime) (h5 : 5 ≤ p) (hp7 : p ≠ 7) :
    ¬ p ^ 2 ∣ 1843262023680 := by
  intro h
  have hmem : p ∈ (1843262023680 : ℕ).primeFactors :=
    Nat.mem_primeFactors.2 ⟨hp, (dvd_pow_self p (by norm_num)).trans h, by norm_num⟩
  rw [show (1843262023680 : ℕ).primeFactors = {2, 3, 5, 7, 11, 19, 31} by
    norm_num [Nat.primeFactors]] at hmem
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · omega
  · omega
  · norm_num at h
  · exact absurd rfl hp7
  · norm_num at h
  · norm_num at h
  · norm_num at h

theorem isPGroup_seven_of_pow_eq_one {G : Type} [Group G] {E : Subgroup G}
    (h : ∀ x ∈ E, x ^ 7 = 1) : IsPGroup 7 E := by
  haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  rw [IsPGroup.iff_orderOf]
  intro g
  have hg : orderOf g ∣ 7 := orderOf_dvd_iff_pow_eq_one.mpr (by
    apply Subtype.ext
    rw [Subgroup.coe_pow, Subgroup.coe_one]
    exact h g g.2)
  rcases (Nat.dvd_prime (by norm_num : Nat.Prime 7)).1 hg with h1 | h7
  · exact ⟨0, by rw [h1, pow_zero]⟩
  · exact ⟨1, by rw [h7, pow_one]⟩

theorem not_sq_dvd_mulAut_of_outer_le_two {S : Type} [Group S] [Finite S]
    (hS : IsSimpleGroup S) (hcard : Nat.card S = 50232960)
    (hOut : Nat.card (Outer S) ≤ 2) {p : ℕ} (hp : p.Prime) (h5 : 5 ≤ p) :
    ¬ p ^ 2 ∣ Nat.card (MulAut S) := by
  have hnab : ∃ a b : S, a * b ≠ b * a := by
    by_contra hc
    push Not at hc
    haveI : IsMulCommutative S := ⟨⟨fun a b => hc a b⟩⟩
    have hprime := (Group.is_simple_iff_prime_card (α := S)).1 hS
    rw [hcard] at hprime
    norm_num at hprime
  have hZ : Subgroup.center S = ⊥ :=
    CFSG.HardMathSupport.Timmesfeld.DefChar.center_eq_bot_of_simple hS hnab
  have hconj : Function.Injective (MulAut.conj : S →* MulAut S) :=
    CFSG.HardMathSupport.Timmesfeld.DefChar.conj_injective_of_center_eq_bot hZ
  have hinner : Nat.card ↥(MulAut.conj : S →* MulAut S).range = Nat.card S :=
    (Nat.card_congr (MonoidHom.ofInjective hconj).toEquiv).symm
  have hMulAut : Nat.card (MulAut S) = Nat.card (Outer S) * Nat.card S := by
    rw [← hinner]
    exact Subgroup.card_eq_card_quotient_mul_card_subgroup _
  rw [hMulAut]
  intro hd
  have hOut12 : Nat.card (Outer S) = 1 ∨ Nat.card (Outer S) = 2 := by
    have := Nat.card_pos (α := Outer S)
    omega
  rcases hOut12 with h1 | h2
  · rw [h1, one_mul, hcard] at hd
    exact not_sq_dvd_50232960 hp h5 hd
  · rw [h2, hcard, show 2 * 50232960 = 100465920 by norm_num] at hd
    exact not_sq_dvd_100465920 hp h5 hd

theorem not_sq_dvd_mulAut_PSp43 {p : ℕ} (hp : p.Prime) (h5 : 5 ≤ p) :
    ¬ p ^ 2 ∣ Nat.card (MulAut CFSG.GH74.Exceptional.PSp43) := by
  have hle : Nat.card (MulAut CFSG.GH74.Exceptional.PSp43) ≤ 51840 :=
    CFSG.Quasithin.SimsF5.card_mulAut_of_mulEquiv_PSp43 (MulEquiv.refl _)
  obtain ⟨m, hm⟩ := dvd_25920_mulAut_PSp43
  have hmpos : 0 < m := by
    rcases Nat.eq_zero_or_pos m with h0 | h
    · rw [h0, mul_zero] at hm
      have := Nat.card_pos (α := MulAut CFSG.GH74.Exceptional.PSp43)
      omega
    · exact h
  have hmle : m ≤ 2 := by omega
  interval_cases m
  · rw [hm, mul_one]
    exact not_sq_dvd_25920 hp h5
  · rw [hm, show 25920 * 2 = 51840 by norm_num]
    exact not_sq_dvd_51840 hp h5

theorem pRank_mulAut_PSp43_le_one {p : ℕ} (hp : p.Prime) (h5 : 5 ≤ p) :
    CFSG.Open.pRank p (⊤ : Subgroup (MulAut CFSG.GH74.Exceptional.PSp43)) ≤ 1 :=
  CFSG.HardMathSupport.Timmesfeld.Tables.Alt.pRank_top_le_of_not_dvd hp.one_lt
    (not_sq_dvd_mulAut_PSp43 hp h5)

theorem k5U42_holds : K5U42 := by
  intro Y _ _ hq _ hmodel p hp h5
  rw [CFSG.SectionRank.pRank_coe_eq_openPRank p (⊤ : Subgroup (MulAut Y))]
  haveI : Group.IsPerfect Y := hq.1
  obtain ⟨e⟩ := psp43_equiv_of_lieModel hmodel
  have hinj : CFSG.Open.pRank p (⊤ : Subgroup (MulAut Y)) ≤
      CFSG.Open.pRank p (⊤ : Subgroup (MulAut (Y ⧸ center Y))) :=
    CFSG.SectionRank.pRank_top_le_of_injective hp.one_lt
      (CFSG.ComponentClassification.PerfectAutomorphisms.centerQuotientHom Y)
      (CFSG.ComponentClassification.PerfectAutomorphisms.centerQuotientHom_injective Y)
  have heq : CFSG.Open.pRank p (⊤ : Subgroup (MulAut (Y ⧸ center Y))) =
      CFSG.Open.pRank p (⊤ : Subgroup (MulAut CFSG.GH74.Exceptional.PSp43)) :=
    CFSG.SectionRank.pRank_top_eq_of_mulEquiv hp.one_lt (MulAut.congr e)
  calc CFSG.Open.pRank p (⊤ : Subgroup (MulAut Y))
      ≤ CFSG.Open.pRank p (⊤ : Subgroup (MulAut (Y ⧸ center Y))) := hinj
    _ = CFSG.Open.pRank p (⊤ : Subgroup (MulAut CFSG.GH74.Exceptional.PSp43)) := heq
    _ ≤ 1 := pRank_mulAut_PSp43_le_one hp h5

theorem k5L227_holds : K5L227 := by
  intro Y _ _ hq _ hmodel p hp h5
  rw [CFSG.SectionRank.pRank_coe_eq_openPRank p (⊤ : Subgroup (MulAut Y))]
  haveI : Group.IsPerfect Y := hq.1
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨e⟩ := CFSG.GH74.KGroups.PSL2.psl2_equiv_of_lieModel (F := GaloisField 3 3) 3 3
    (by norm_num) (by rw [GaloisField.card 3 3 (by norm_num)]) hmodel
  have hinj : CFSG.Open.pRank p (⊤ : Subgroup (MulAut Y)) ≤
      CFSG.Open.pRank p (⊤ : Subgroup (MulAut (Y ⧸ center Y))) :=
    CFSG.SectionRank.pRank_top_le_of_injective hp.one_lt
      (CFSG.ComponentClassification.PerfectAutomorphisms.centerQuotientHom Y)
      (CFSG.ComponentClassification.PerfectAutomorphisms.centerQuotientHom_injective Y)
  have hcard : Nat.card (MulAut (CFSG.AGLEmbedding.PSL2GF 3 3)) = 58968 := by
    rw [CFSG.AGLEmbedding.card_mulAut_psl2GF 3 3 (by norm_num)]
    norm_num
  have heq : CFSG.Open.pRank p (⊤ : Subgroup (MulAut (Y ⧸ center Y))) =
      CFSG.Open.pRank p (⊤ : Subgroup (MulAut (CFSG.AGLEmbedding.PSL2GF 3 3))) :=
    CFSG.SectionRank.pRank_top_eq_of_mulEquiv hp.one_lt (MulAut.congr e)
  have hbound : CFSG.Open.pRank p (⊤ : Subgroup (MulAut (CFSG.AGLEmbedding.PSL2GF 3 3))) ≤ 1 :=
    CFSG.HardMathSupport.Timmesfeld.Tables.Alt.pRank_top_le_of_not_dvd hp.one_lt (by
      rw [hcard]
      exact not_sq_dvd_58968 hp h5)
  calc CFSG.Open.pRank p (⊤ : Subgroup (MulAut Y))
      ≤ CFSG.Open.pRank p (⊤ : Subgroup (MulAut (Y ⧸ center Y))) := hinj
    _ = CFSG.Open.pRank p (⊤ : Subgroup (MulAut (CFSG.AGLEmbedding.PSL2GF 3 3))) := heq
    _ ≤ 1 := hbound

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82
