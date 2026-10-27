module

public import CFSG.LocalAnalysis.UniquenessCase.UCKQSCrossTools
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosureLieExcG2
public import CFSG.RankThree.PartOne.K128.ReeShape
import CFSG.LieType.SeitzGeneration.ExcReeG2Rank
public import CFSG.LieType.SeitzGeneration.ExcTorusTwE6Three
public import CFSG.LieType.SeitzGeneration.ExcTorusTwE6Four
public import CFSG.RankThree.PartOne.K128.D4Syl
public import CFSG.LocalAnalysis.UniquenessCase.UCKQSDispatch

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UCK

open CFSG.Assembly.LowTwoRank CFSG.Blueprint CFSG.Blueprint.Chevalley

theorem PCentralAbelianAt.of_pRank_le_one' {K : Type} [Group K] [Finite K] {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    (h : CFSG.pRank p K ≤ 1) : PCentralAbelianAt K p :=
  PCentralAbelianAt.of_pRank_le_one hp2 (by rwa [← CFSG.SectionRank.pRank_eq_open_pRank_top])

theorem qsExcS_card_lt_of_no_elemAbelian {G : Type} [Group G] {p k : ℕ} (hp : p.Prime)
    (hno : ∀ E : Subgroup G, CFSG.Open.IsElemAbelian p E → Nat.card E = p ^ k → False)
    (F : Subgroup G) (hF : CFSG.Open.IsElemAbelian p F) : Nat.card F < p ^ k := by
  by_contra h
  push Not at h
  obtain ⟨F', hF'⟩ := Sylow.exists_subgroup_card_pow_prime_of_le_card hp hF.isPGroup h
  refine hno (F'.map F.subtype) (hF.mono (Subgroup.map_subtype_le F')) ?_
  rw [Subgroup.card_map_of_injective F.subtype_injective, hF']

theorem qsExcS_rankLE1_of_no_plane {G : Type} [Group G] [Finite G] {p : ℕ} (hp : p.Prime)
    (hno : ∀ E : Subgroup G, CFSG.Open.IsElemAbelian p E → Nat.card E = p ^ 2 → False) :
    CFSG.LieType.SeitzGeneration.RankLE1 p G := by
  intro F hF
  haveI : Fact p.Prime := ⟨hp⟩
  have hlt := qsExcS_card_lt_of_no_elemAbelian hp hno F hF
  obtain ⟨j, hj⟩ := hF.isPGroup.exists_card_eq
  rw [hj] at hlt ⊢
  have : j < 2 := (Nat.pow_lt_pow_iff_right hp.one_lt).1 hlt
  calc p ^ j ≤ p ^ 1 := Nat.pow_le_pow_right hp.pos (by omega)
    _ = p := pow_one p

section Ree

open CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosure.ExcCross.Untw in
theorem qsExcS_pca_G2 (F : Type) [Field F] [Finite F] {p : ℕ} [Fact p.Prime] (hp5 : 5 ≤ p)
    (hpq : ¬ p ∣ Nat.card F) [Finite (adjointGroup .G2 F)] : PCentralAbelianAt (adjointGroup .G2 F) p := by
  have hp : p.Prime := Fact.out
  have hq1 : 1 ≤ Nat.card F := Nat.card_pos
  by_cases hd : p ∣ Nat.card F ^ 2 - 1
  · rcases CFSG.RankThree.PartOne.K128.dvd_pred_or_succ_of_dvd_sq_sub_one hp (by omega) hq1 hd with
      ⟨h1, -⟩ | ⟨h2, -⟩
    · exact PCentralAbelianAt.of_sylowFrameM (G2.sylowFrameM_one hp hp5 h1)
    · exact PCentralAbelianAt.of_sylowFrameM (G2.sylowFrameM_neg hp hp5 h2)
  · exact PCentralAbelianAt.of_rankLE1 (by omega) (rankLE1_G2 hp hp5 hpq hd)

theorem pcaLieCross_G2 : PCALieCrossAt .G2 := by
  intro K _ _ _ _ _ _ _ _ hmodel p hp h5 hpℓ _
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨⟨hℓ, -, -⟩, hm⟩ := hmodel.chevalleyExceptionalModel (by simp [chevalleyExceptionalTags])
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := hm
  have hpq : ¬ p ∣ Nat.card F := by
    rw [hF]
    intro hd
    exact hpℓ ((Nat.prime_dvd_prime_iff_eq hp hℓ).1 (hp.dvd_of_dvd_pow hd))
  let e' : K ≃* adjointGroup .G2 F := e.trans
    ((QuotientGroup.quotientMulEquivOfEq
      (CFSG.LieType.Chevalley.center_adjointGroup_eq_bot (τ := .G2) (K := F))).trans
      QuotientGroup.quotientBot)
  haveI : Finite (adjointGroup .G2 F) := Finite.of_equiv K e'.toEquiv
  exact PCentralAbelianAt.of_mulEquiv e' (qsExcS_pca_G2 F h5 hpq)

theorem pcaLieCross_twistedG2 : PCALieCrossAt .twistedG2 := by
  intro K _ _ _ _ _ ℓ f _ hmodel p hp h5 _ _
  obtain ⟨-, hrt⟩ := hmodel.reeTitsModel (by simp [reeTitsTags])
  obtain ⟨-, -, hℓ, ⟨a', ha', hfa'⟩, hiso⟩ := CFSG.LieType.Ree.small_Ree_model_Schreier K ℓ f hrt
  subst hℓ
  obtain ⟨-, a, hfa, X, _, _, hXcard, ⟨e2⟩⟩ := hrt
  have ha : 1 ≤ a := by omega
  haveI : Fintype X := Fintype.ofFinite X
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hchar : CharP X CFSG.LieType.Ree.ReeTag.G2.prime :=
    charP_of_card_eq_prime_pow (p := 3) (f := f) (by rw [← Nat.card_eq_fintype_card, hXcard])
  obtain ⟨E⟩ := hiso a X hfa hXcard ⟨e2⟩
  have hX : Nat.card X = 3 ^ (2 * a + 1) := by rw [← hfa]; exact hXcard
  have hp3 : 3 < p := by omega
  haveI : Fact p.Prime := ⟨hp⟩
  refine PCentralAbelianAt.of_rankLE1 (by omega) (qsExcS_rankLE1_of_no_plane hp ?_)
  intro F' hF' hFc
  have hF₁ : CFSG.Open.IsElemAbelian p (F'.map E.toMonoidHom) := hF'.map E.toMonoidHom
  have hF₂ : CFSG.Open.IsElemAbelian p ((F'.map E.toMonoidHom).map
      (CFSG.LieType.Ree.ReeTag.G2.reeGamma X a).subtype) := hF₁.map _
  refine CFSG.LieType.SeitzGeneration.no_plane_reeGamma_G2 ha hX hp hp3
    (Subgroup.map_subtype_le _) hF₂.isElementaryAbelian ?_
  rw [Subgroup.card_map_of_injective (CFSG.LieType.Ree.ReeTag.G2.reeGamma X a).subtype_injective,
    Subgroup.card_map_of_injective E.injective, hFc]

end Ree

section TwistedF4

open CFSG.LieType.Chevalley CFSG.LieType.Ree CFSG.RankThree.PartOne.K128 CFSG.RankThree.LargeReeOrder

theorem qsExcS_pca_reeGamma {a : ℕ} {K : Type} [Field K] [Finite K] [CharP K ReeTag.F4.prime]
    [Finite (ReeTag.F4.reeGamma K a)] (hK : Nat.card K = 2 ^ (2 * a + 1))
    {p : ℕ} [Fact p.Prime] (h5 : 5 ≤ p) : PCentralAbelianAt (ReeTag.F4.reeGamma K a) p := by
  have hp : p.Prime := Fact.out
  have hp2 : p ≠ 2 := by omega
  by_cases hdvd : p ∣ Nat.card (ReeTag.F4.reeGamma K a)
  · obtain ⟨-, hfac⟩ := large_Ree_exact_native_order_and_prime_factor_exhaustion a K hK
    rcases hfac p hp (by omega) hdvd with h | h | h | h | h
    · exact PCentralAbelianAt.of_sylowShape (sylowShape_ree_phi1 hK hp h5 h)
    · exact PCentralAbelianAt.of_sylowShape (sylowShape_ree_phi2 hK hp h5 h)
    · exact PCentralAbelianAt.of_sylowShape (sylowShape_ree_phi4 hK hp h5 h)
    · exact PCentralAbelianAt.of_pRank_le_one' hp2 (pRank_le_one_ree_phi6 hK hp h5 h)
    · exact PCentralAbelianAt.of_pRank_le_one' hp2 (pRank_le_one_ree_phi12 hK hp h5 h)
  · apply PCentralAbelianAt.of_factorization_le hp2
    rw [Nat.factorization_eq_zero_of_not_dvd hdvd]
    omega

theorem pcaLieCross_twistedF4 : PCALieCrossAt .twistedF4 := by
  intro X _ _ _ _ _ ℓ f hadm hmodel p hp h5 _ _
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨-, hrt⟩ := hmodel.reeTitsModel (by simp [reeTitsTags])
  obtain ⟨-, -, -, hℓ, -, -⟩ := hadm
  subst hℓ
  obtain ⟨a, K, _, _, _, ha, hfa, hK, ⟨e⟩⟩ := CFSG.RankThree.PartOne.KEXC.exists_gamma_of_model hrt
  have hK' : Nat.card K = 2 ^ (2 * a + 1) := by rw [← hfa]; exact hK
  haveI : Finite (ModGL ReeTag.F4.tag K) := finite_modGL
  haveI : Finite (ReeTag.F4.reeGamma K a) := Subtype.finite
  exact PCentralAbelianAt.of_mulEquiv e (qsExcS_pca_reeGamma hK' h5)

end TwistedF4

section Suzuki

private local instance : DecidableEq (Equiv.Perm (Fin 3)) :=
  Fintype.decidableEqEquivFintype

private theorem qsExcS_certificate43_of_decide :
      ∀ s t : Equiv.Perm (Fin 3),
        (s ≠ 1 ∧ s ^ 2 = 1) → (t ≠ 1 ∧ t ^ 2 = 1) → s ≠ t →
          (s * t) ^ 3 = 1 ∧ s * t ≠ 1 := by
  decide +kernel

theorem pcaLieCross_twistedB2 : PCALieCrossAt .twistedB2 := by
  intro K _ _ _ _ _ ℓ f _ hmodel p hp _ hpℓ _
  haveI : Fact p.Prime := ⟨hp⟩
  haveI := qsExcS_certificate43_of_decide
  have hS : SuzukiModel K ℓ f := by
    rcases hmodel with ⟨ht, -⟩ | ⟨-, ht, -⟩ | ⟨-, ht, -⟩ | ⟨-, -, hS⟩
    · exact absurd ht (by decide)
    · exact absurd ht (by decide)
    · exact absurd ht (by decide)
    · exact hS
  obtain ⟨hℓ, a, ha, F, _, _, hfa, hcard, ⟨e⟩⟩ := hS
  subst hℓ
  have hF : Nat.card F = 2 ^ (2 * a + 1) := by rw [hcard, hfa]
  let e' : K ≃* CFSG.Open.GLASzGroup a F :=
    e.trans (MulEquiv.subgroupCongr (CFSG.LieType.BorelTits.suzukiGroup_eq_glaSzGroup a F))
  have hsyl := CFSG.ProperTwoGeneratedCore.LocalCriterionDenominator.suzuki_model_oddSylow_cyclic
    a ha hF e' p hpℓ
  refine PCentralAbelianAt.of_sylow_comm fun S => ?_
  haveI := hsyl S
  infer_instance

end Suzuki

theorem qsExcS_factorization_titsOrder_le (p : ℕ) (hp : p.Prime) (h5 : 5 ≤ p) :
    (17971200 : ℕ).factorization p ≤ 3 := by
  by_contra h
  push Not at h
  have h4 : p ^ 4 ∣ 17971200 := (hp.pow_dvd_iff_le_factorization (by norm_num)).2 h
  have hle : p ^ 4 ≤ 17971200 := Nat.le_of_dvd (by norm_num) h4
  have hp65 : p ≤ 65 := by
    by_contra hc
    push Not at hc
    have : 66 ^ 4 ≤ p ^ 4 := Nat.pow_le_pow_left hc 4
    omega
  interval_cases p <;> norm_num at h4

section Tits


theorem pcaLieCross_Tits : PCALieCrossAt .Tits := by
  intro K _ _ _ _ _ _ f hadm hmodel p hp h5 _ _
  obtain ⟨-, hrt⟩ := hmodel.reeTitsModel (by simp [reeTitsTags])
  obtain ⟨-, -, -, hℓ, -⟩ := hadm
  subst hℓ
  obtain ⟨e⟩ := CFSG.Sporadic.Schreier.Tits.titsModelEquiv K 2 f hrt
  have hcard : Nat.card K = 17971200 := by
    rw [Nat.card_congr e.toEquiv]
    exact CFSG.Sporadic.Schreier.Tits.card_titsD
  haveI : Fact p.Prime := ⟨hp⟩
  exact PCentralAbelianAt.of_factorization_le (by omega)
    (by rw [hcard]; exact qsExcS_factorization_titsOrder_le p hp h5)

end Tits

open CFSG.LieType.Chevalley CFSG.LieType.SeitzGeneration CFSG.HardMathSupport.Timmesfeld.CrossChar Polynomial
open CFSG.RankThree.Chevalley (exhaustionPhi exact_E_type_and_triality_cross_prime_factor_exhaustion)

open CFSG.RankThree.PartOne.K128 (sylowShape_D4 pRank_le_one_D4_twelve dvd_phiNat_of_dvd_cycloVal)


theorem qsExcS_degCountTw_eq_two {e : ℕ} (h : degCountTw e = 2) : e = 3 ∨ e = 4 := by
  have h60 := le_sixty_of_degCountTw_pos (e := e) (by omega)
  have key : ∀ e ≤ 60, degCountTw e = 2 → e = 3 ∨ e = 4 := by decide
  exact key e h60 h

section TwistedE6

theorem qsExcS_pca_twistedE6_group {ℓ f : ℕ} (hℓ : ℓ.Prime) (hf : 1 ≤ f) (F : Type) [Field F]
    (hF : Nat.card F = (ℓ ^ f) ^ 2) (σ : F ≃+* F) (hσ : ∀ c, σ c = c ^ (ℓ ^ f))
    [Finite (twistedE6RootGroup F σ)] {p : ℕ} (hp : p.Prime) (h5 : 5 ≤ p) (hpℓ : p ≠ ℓ) :
    PCentralAbelianAt (twistedE6RootGroup F σ) p := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hpq : ¬ p ∣ ℓ ^ f := fun h =>
    hpℓ ((Nat.prime_dvd_prime_iff_eq hp hℓ).1 (hp.dvd_of_dvd_pow h))
  obtain ⟨e, he⟩ : ∃ e, orderOf (((ℓ ^ f : ℕ)) : ZMod p) = e := ⟨_, rfl⟩
  by_cases h3 : 3 ≤ degCountTw e
  · rcases eq_of_three_le_degCountTw h3 with rfl | rfl | rfl
    ·
      obtain ⟨E, hE, hc⟩ := exists_elemAbelian_twistedE6_one hℓ hf F hF σ hσ hp (by omega) he
      exact PCentralAbelianAt.of_elemAbelian hp hE hc (by norm_num)
    ·
      obtain ⟨E, hE, hc⟩ := exists_elemAbelian_twistedE6_two hℓ hf F hF σ hσ hp (by omega) he
      exact PCentralAbelianAt.of_elemAbelian hp hE hc (by norm_num)
    ·
      have h7 : 7 ≤ p := by
        haveI : Fact p.Prime := ⟨hp⟩
        have hne : (((ℓ ^ f : ℕ)) : ZMod p) ≠ 0 := fun h0 =>
          hpq ((ZMod.natCast_eq_zero_iff _ _).1 h0)
        have hdvd := ZMod.orderOf_dvd_card_sub_one hne
        rw [he] at hdvd
        have := Nat.le_of_dvd (by omega) hdvd
        omega
      obtain ⟨m, hm⟩ :=
        exists_sylowTorus_twistedE6 hℓ hf F hF σ hσ hp h7 hpq (by rw [he]; exact h3)
      exact PCentralAbelianAt.of_sylowTorus hm
  ·
    by_cases h1 : degCountTw e ≤ 1
    · exact PCentralAbelianAt.of_rankLE1 (by omega)
        (rankLE1_twistedE6 hℓ hf F hF σ hσ hp hpq (by rw [he]; exact h1))
    · rcases qsExcS_degCountTw_eq_two (e := e) (by omega) with rfl | rfl
      · exact PCentralAbelianAt.of_sylowTorus (sylowTorus_twistedE6_three hℓ hf F hF σ hσ hp he)
      · exact PCentralAbelianAt.of_sylowTorus (sylowTorus_twistedE6_four hℓ hf F hF σ hσ hp he)

theorem pcaLieCross_twistedE6 : PCALieCrossAt .twistedE6 := by
  intro K _ _ _ _ n ℓ f _ hmodel p hp h5 hpℓ _
  obtain ⟨⟨hℓ, hf, _⟩, hm⟩ :=
    hmodel.chevalleyExceptionalModel (by simp [chevalleyExceptionalTags])
  obtain ⟨F, _, _, σ, hF, hσ, ⟨e⟩⟩ := exists_mulEquiv_graphFixedRootGroup_card .E6 hℓ hf hm
  haveI : Finite (twistedE6RootGroup F σ) := Finite.of_equiv K e.toEquiv
  haveI : Fact p.Prime := ⟨hp⟩
  exact PCentralAbelianAt.of_mulEquiv e (qsExcS_pca_twistedE6_group hℓ hf F hF σ hσ hp h5 hpℓ)

end TwistedE6

section TrialityD4

theorem pcaLieCross_trialityD4 : PCALieCrossAt .trialityD4 := by
  intro K _ _ _ _ n ℓ f _ hmodel p hp h5 hpℓ hpK
  have hch := hmodel.chevalleyExceptionalModel (by simp [chevalleyExceptionalTags])
  have hℓ : ℓ.Prime := hch.1.1
  have hf : 1 ≤ f := hch.1.2.1
  haveI : Fact ℓ.Prime := ⟨hℓ⟩
  obtain ⟨F, _, _, σ, hF, hσ, ⟨e⟩⟩ := exists_mulEquiv_graphFixedRootGroup_card .D4 hℓ hf hch.2
  have hF3 : Nat.card F = (ℓ ^ f) ^ 3 := hF
  haveI : Finite (graphFixedRootGroup TwistTag.D4 F σ.toRingHom) := Finite.of_equiv K e.toEquiv
  haveI : Fact p.Prime := ⟨hp⟩
  refine PCentralAbelianAt.of_mulEquiv e ?_
  obtain ⟨m, hm, hd⟩ := ((exact_E_type_and_triality_cross_prime_factor_exhaustion hp (by omega)
    (Ne.symm hpℓ) hch).1 hpK).2.2.2.2 rfl
  have hq1 : 1 ≤ ℓ ^ f := Nat.one_le_pow _ _ hℓ.pos
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  by_cases h12 : m = 12
  ·
    subst h12
    have h24 : (ℓ ^ f) ^ 2 ≤ (ℓ ^ f) ^ 4 := Nat.pow_le_pow_right hq1 (by omega)
    have h1 : (p : ℤ) ∣ (((ℓ ^ f) ^ 4 - (ℓ ^ f) ^ 2 + 1 : ℕ) : ℤ) := by
      rw [Nat.cast_add, Nat.cast_sub h24]
      push_cast
      simpa only [exhaustionPhi, eval_add, eval_sub, eval_pow, eval_X, eval_one,
        Nat.cast_pow] using hd
    exact PCentralAbelianAt.of_pRank_le_one' (by omega)
      (pRank_le_one_D4_twelve hℓ hf F hF3 σ hσ hp h5 (Int.natCast_dvd_natCast.1 h1))
  ·
    have hm' : m = 1 ∨ m = 2 ∨ m = 3 ∨ m = 6 := by omega
    exact PCentralAbelianAt.of_sylowShape
      (sylowShape_D4 hf F hF3 σ hσ hm' hp h5 (dvd_phiNat_of_dvd_cycloVal hq1 hm' hd))

end TrialityD4

end CFSG.LocalAnalysis.UniquenessCase.UCK
