module

public import CFSG.LocalAnalysis.UniquenessCase.UC6Syl
public import CFSG.Goldschmidt.Steps.G310Basic
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.DataThree
public import CFSG.LocalAnalysis.UniquenessCase.UC6Inst

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open Subgroup CFSG.ABGLocalTools CFSG.LocalAnalysis.RankThreeUC
open CFSG.RankThreeCoreUniqueness.Helpers
  (gamma_le_iff gamma_normalizer_le pRank_set_bddAbove pRank_attained pRank_eq_of_subgroup_equiv
    elementary_isPGroup elementary_map_injective)

variable {G : Type} [Group G] [Finite G]

structure Sigma23Std (D : Data G) : Prop where
  sig3_sub : D.sig3 ⊆ {3}
  gamma_two : ∀ p ∈ D.sig, ∀ P : Subgroup G, IsSylowOf p P D.M → rankThreeGamma 2 p P ≤ D.M

theorem uc22p22q_pRank_le_sylow {p : ℕ} [Fact p.Prime] {M P : Subgroup G} (hP : IsSylowOf p P M) :
    CFSG.Open.pRank p M ≤ CFSG.Open.pRank p P := by
  rcases Nat.eq_zero_or_pos (CFSG.Open.pRank p M) with h0 | hpos
  · rw [h0]
    exact Nat.zero_le _
  obtain ⟨E, hEM, hE, hcard⟩ := pRank_attained p M hpos
  obtain ⟨k, -, hk⟩ := UC6.exists_conj_le_of_isSylowOf hP hEM (elementary_isPGroup p E hE)
  let f : G →* G := (MulAut.conj k⁻¹).toMonoidHom
  have hf : Function.Injective f := (MulAut.conj k⁻¹).injective
  have hEP : E.map f ≤ P := by
    rintro _ ⟨x, hx, rfl⟩
    simpa [f, MulAut.conj_apply] using hk x hx
  unfold CFSG.Open.pRank
  refine le_csSup (pRank_set_bddAbove p (Fact.out : p.Prime).one_lt P)
    ⟨E.map f, hEP, elementary_map_injective p E f hf hE, ?_⟩
  rw [Subgroup.card_map_of_injective hf]
  exact hcard

theorem uc22p22q_isSylowOf_top_of_normalizer {p : ℕ} [Fact p.Prime] {M P : Subgroup G}
    (hP : IsSylowOf p P M) (hN : normalizer (P : Set G) ≤ M) : IsSylowOf p P ⊤ := by
  obtain ⟨S, hPS⟩ := hP.isPGroup.exists_le_sylow
  have hPS' : P ≤ (S : Subgroup G) := hPS
  have hEq : P = (S : Subgroup G) := by
    by_contra hne
    have hlt := CFSG.Goldschmidt.G310.lt_inf_normalizer S.isPGroup' hPS' hne
    have hle : (S : Subgroup G) ⊓ normalizer (P : Set G) ≤ M := inf_le_right.trans hN
    have hpg : IsPGroup p ↥((S : Subgroup G) ⊓ normalizer (P : Set G)) := S.isPGroup'.to_inf_left
    exact hlt.ne (hP.eq_of_le hlt.le hle hpg).symm
  rw [isSylowOf_iff]
  refine ⟨le_top, hP.isPGroup, ?_⟩
  rw [hEq]
  simpa [Subgroup.relIndex_top_right] using S.not_dvd_index

theorem uc22p22q_isSylowOf_top (D : Data G) (hstd : Sigma23Std D) {p : ℕ} (hp : p ∈ D.sig)
    {P : Subgroup G} (hP : IsSylowOf p P D.M) : IsSylowOf p P ⊤ := by
  haveI : Fact p.Prime := ⟨(D.sig_prime p hp).1⟩
  have h2 : 2 ≤ CFSG.Open.pRank p P := (D.sig_rank p hp).trans (uc22p22q_pRank_le_sylow hP)
  exact uc22p22q_isSylowOf_top_of_normalizer hP
    ((gamma_normalizer_le 2 p P P le_rfl h2).trans (hstd.gamma_two p hp P hP))

theorem uc22p22q_gamma_two_of_exists {p : ℕ} [Fact p.Prime] {M Q P : Subgroup G} (hQ : IsSylowOf p Q M)
    (hΓ : rankThreeGamma 2 p Q ≤ M) (hP : IsSylowOf p P M) : rankThreeGamma 2 p P ≤ M := by
  obtain ⟨k, hkM, hk⟩ := hQ.exists_mem_conj hP
  refine (gamma_le_iff 2 p P M).2 fun Y hYP hY2 => ?_
  let f : G →* G := (MulAut.conj k⁻¹).toMonoidHom
  have hf : Function.Injective f := (MulAut.conj k⁻¹).injective
  have hmem : ∀ h : G, h ∈ Y.map f ↔ k * h * k⁻¹ ∈ Y := by
    intro h
    constructor
    · rintro ⟨y, hy, rfl⟩
      simpa [f, MulAut.conj_apply, mul_assoc] using hy
    · intro hh
      exact ⟨k * h * k⁻¹, hh, by simp [f, MulAut.conj_apply, mul_assoc]⟩
  have hYQ : Y.map f ≤ Q := by
    intro h hh
    have := (hk (k * h * k⁻¹)).1 (hYP ((hmem h).1 hh))
    simpa [mul_assoc] using this
  have hrank : CFSG.Open.pRank p (Y.map f) = CFSG.Open.pRank p Y :=
    (pRank_eq_of_subgroup_equiv p (Fact.out : p.Prime).one_lt Y (Y.map f)
      (Subgroup.equivMapOfInjective Y f hf)).symm
  have hN : normalizer ((Y.map f : Subgroup G) : Set G) ≤ M :=
    (gamma_normalizer_le 2 p Q (Y.map f) hYQ (hrank ▸ hY2)).trans hΓ
  intro g hg
  have hg' : k⁻¹ * g * k ∈ normalizer ((Y.map f : Subgroup G) : Set G) := by
    rw [mem_normalizer_iff]
    intro h
    rw [hmem, hmem]
    have hgY := mem_normalizer_iff.1 hg (k * h * k⁻¹)
    have e : k * (k⁻¹ * g * k * h * (k⁻¹ * g * k)⁻¹) * k⁻¹ = g * (k * h * k⁻¹) * g⁻¹ := by group
    rw [e]
    exact hgY
  have hmg := hN hg'
  have e : g = k * (k⁻¹ * g * k) * k⁻¹ := by group
  rw [e]
  exact M.mul_mem (M.mul_mem hkM hmg) (M.inv_mem hkM)

theorem uc22p22q_isSylowOf_of_sylow {p : ℕ} [Fact p.Prime] {M : Subgroup G} (Q : Sylow p G)
    (hQM : (Q : Subgroup G) ≤ M) : IsSylowOf p (Q : Subgroup G) M :=
  (isSylowOf_iff.2 ⟨le_top, Q.isPGroup', by simpa [Subgroup.relIndex_top_right] using Q.not_dvd_index⟩ :
    IsSylowOf p (Q : Subgroup G) ⊤).of_le hQM le_top

theorem sigma23Std_ofSetup (hS : Standing G) (S : Setup G) :
    Sigma23Std (PartTwo.Three.dataOfSetup hS S) where
  sig3_sub := fun q hq => Set.mem_singleton_iff.2 hq.1
  gamma_two := fun p hp P hP => by
    obtain ⟨hpA, Q, hw⟩ := hp
    haveI : Fact p.Prime := ⟨(PartTwo.Three.prime_of_mem_rankThreeSigmaA hpA).1⟩
    have h3 : 3 ≤ CFSG.Open.pRank p (Q : Subgroup G) :=
      CFSG.RankThreeCoreUniqueness.Helpers.selected_sylow_rank_at_least_three hS.rank p hpA Q
    have hQM : (Q : Subgroup G) ≤ S.M :=
      le_normalizer.trans ((gamma_normalizer_le 2 p (Q : Subgroup G) (Q : Subgroup G) le_rfl
        (by omega)).trans hw.u0)
    exact uc22p22q_gamma_two_of_exists (uc22p22q_isSylowOf_of_sylow Q hQM) hw.u0 hP

open CFSG.Yardstones.Mf4cdcdf2e013 (Standing4 Setup4) in
theorem sigma23Std_ofSetup4 (hS : Standing4 G) (hU : CFSG.Open.uniqueFourUnique G) (S : Setup4 G) :
    Sigma23Std (CFSG.LocalAnalysis.UniquenessCase.UC6.dataOfSetup4 hS hU S) where
  sig3_sub := fun _ hq => absurd hq (by simp [CFSG.LocalAnalysis.UniquenessCase.UC6.dataOfSetup4])
  gamma_two := fun p hp P hP => by
    obtain ⟨-, -, -, Q, hQM, hΓ, -⟩ := (hU S.M S.maxLocal ⟨p, hp⟩).1 p hp
    haveI : Fact p.Prime := ⟨hp.1.1⟩
    exact uc22p22q_gamma_two_of_exists (uc22p22q_isSylowOf_of_sylow Q hQM) hΓ hP

end CFSG.LocalAnalysis.UniquenessCase.UC22
