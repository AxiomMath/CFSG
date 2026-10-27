module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S2112aR34F2Even2NoSwap
public import CFSG.LocalAnalysis.UniquenessCase.FundamentalLie
public import CFSG.LocalAnalysis.UniquenessCase.UCFront14
import CFSG.LocalAnalysis.UniquenessCase.UC22S2112aR34F2Even2Rho
import CFSG.LocalAnalysis.UniquenessCase.UC22FunCountAmbient
import CFSG.LocalAnalysis.UniquenessCase.UC22FunSplitAmbient
import CFSG.Quasithin.Vol2.KGFactInspOddCore
import CFSG.LocalAnalysis.ComponentInitial.BlockTwoFactorSylowShape
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open Subgroup
open CFSG.Blueprint (LieModel)
open scoped MatrixGroups Pointwise

private lemma uc22s2112r34_excns_factorization_pow_two {p k : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    (p ^ k).factorization 2 = 0 :=
  Nat.factorization_eq_zero_of_not_dvd (hp.odd_of_ne_two hp2).pow.not_two_dvd_nat

private lemma uc22s2112r34_excns_factorization_pow_six_sub_one {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) :
    (p ^ 6 - 1).factorization 2 = (p ^ 2 - 1).factorization 2 := by
  have hpodd : Odd p := hp.odd_of_ne_two hp2
  have hsq : 1 < p ^ 2 := by
    have h : 2 * 2 ≤ p * p := Nat.mul_le_mul hp.two_le hp.two_le
    rw [pow_two]
    omega
  have hA : p ^ 2 - 1 ≠ 0 := by omega
  have hB : p ^ 4 + p ^ 2 + 1 ≠ 0 := by positivity
  have hBodd : Odd (p ^ 4 + p ^ 2 + 1) :=
    ((hpodd.pow (n := 4)).add_odd (hpodd.pow (n := 2))).add_one
  have hBfac : (p ^ 4 + p ^ 2 + 1).factorization 2 = 0 :=
    Nat.factorization_eq_zero_of_not_dvd hBodd.not_two_dvd_nat
  have hid : p ^ 6 - 1 = (p ^ 2 - 1) * (p ^ 4 + p ^ 2 + 1) := by
    have h := geom_sum_mul_of_one_le (x := p ^ 2) (by omega) 3
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, pow_zero, pow_one,
      zero_add] at h
    have h24 : (p ^ 2) ^ 2 = p ^ 4 := by ring
    have h26 : (p ^ 2) ^ 3 = p ^ 6 := by ring
    rw [h24, h26] at h
    rw [mul_comm (p ^ 2 - 1),
      show p ^ 4 + p ^ 2 + 1 = 1 + p ^ 2 + p ^ 4 by ring]
    exact h.symm
  rw [hid, Nat.factorization_mul hA hB, Finsupp.add_apply, hBfac, add_zero]

private lemma uc22s2112r34_excns_odd_pow_eight_add {p : ℕ} (hpodd : Odd p) :
    Odd (p ^ 8 + p ^ 4 + 1) :=
  ((hpodd.pow (n := 8)).add_odd (hpodd.pow (n := 4))).add_one

private lemma uc22s2112r34_excns_two_dvd_card_inf_of_equiv {X : Type} [Group X]
    {F : Type} [Field F] (h2 : (2 : F) ≠ 0) {K₁ K₂ : Subgroup X}
    (e : K₁ ≃* SL(2, F)) (hC : centralizer (K₁ : Set X) ≤ K₂) :
    2 ∣ Nat.card ↥(K₁ ⊓ K₂) := by
  let z₁ : K₁ := e.symm (-1)
  have hz : e z₁ = -1 := e.apply_symm_apply (-1)
  have hmem : (-1 : SL(2, F)) ∈ Subgroup.center SL(2, F) :=
    CFSG.ClassicalInvolution.QuaternionStructure.mem_center_specialLinearGroup_two_iff.mpr
      (Or.inr rfl)
  have hcentralK : z₁ ∈ Subgroup.center K₁ := by
    rw [Subgroup.mem_center_iff]
    intro k
    apply e.injective
    rw [map_mul, map_mul, hz]
    exact Subgroup.mem_center_iff.mp hmem (e k)
  have hcentral : ((z₁ : K₁) : X) ∈ centralizer (K₁ : Set X) := by
    rw [Subgroup.mem_centralizer_iff]
    intro k hk
    exact congrArg Subtype.val (Subgroup.mem_center_iff.mp hcentralK ⟨k, hk⟩)
  have hzK : ((z₁ : K₁) : X) ∈ K₁ ⊓ K₂ := ⟨z₁.2, hC hcentral⟩
  have hord : orderOf ((z₁ : K₁) : X) = 2 := by
    have h1 : orderOf z₁ = 2 := by
      rw [← MulEquiv.orderOf_eq e z₁, hz,
        CFSG.ClassicalInvolution.QuaternionStructure.orderOf_neg_one_specialLinearGroup_two h2]
    rw [Subgroup.orderOf_coe, h1]
  rw [← hord]
  exact Subgroup.orderOf_dvd_natCard (K₁ ⊓ K₂) hzK


theorem uc22s2112r34_exc_nonempty_equiv_sl2 {X : Type} [Group X] [Finite X] [IsSimpleGroup X]
    {t : StatedLieTag} {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (ht : t = .G2 ∨ t = .trialityD4)
    (hX : LieModel X t 0 p 1) {K : Subgroup X} (hK : IsFundamentalOver p K) :
    Nonempty (K ≃* SL(2, GaloisField p 1)) ∨
      (t = .trialityD4 ∧ Nonempty (K ≃* SL(2, GaloisField p 3))) := by
  have hp : p.Prime := Fact.out
  have hp3 : 3 ≤ p := by
    have := hp.two_le
    omega
  have hadm : StatedLieAdmissible t 0 p 1 := by
    rcases ht with rfl | rfl
    · exact ⟨hp, le_rfl, rfl, by rw [pow_one]; exact hp3⟩
    · exact ⟨hp, le_rfl, rfl⟩
  have hfund : CFSG.ClassicalInvolution.Generic.IsFundTag t := by
    rcases ht with rfl | rfl <;> trivial
  have hA1 : ¬ (t = .PSL ∧ 0 = 2) := by
    rintro ⟨h, -⟩
    rcases ht with rfl | rfl <;> cases h
  have hK' : IsFundamentalOver (p ^ 1) K := by rwa [pow_one]
  obtain ⟨-, -, hL2, -⟩ := fundamental_ambient_of_lieModel hp hp2 hadm hX hA1 hK'
  obtain ⟨ψ, hψ, hker⟩ :=
    CFSG.ClassicalInvolution.Upgrade.lieModelCentralCover t 0 p 1 hp hp2 hfund hadm X hX
  obtain ⟨R, hR, hKR, hRk⟩ :=
    exists_mem_fundamentalSubgroups_of_isFundamentalOver_general hp hp2 hadm hX hfund hA1 hL2
      ψ hψ hker hK'
  have eK : K ≃* R := by
    subst hKR
    exact (CFSG.LocalAnalysis.ComponentInitial.equivMapOfInfKerEqBot ψ hRk).symm
  rcases
    CFSG.ClassicalInvolution.ModelFacts.nonempty_equiv_sl2_galoisField_of_mem_fundamentalSubgroups
      hp2 hfund hadm hR with h | ⟨h, h2⟩
  · obtain ⟨e⟩ := h
    exact Or.inl ⟨eK.trans e⟩
  · obtain ⟨e⟩ := h2
    exact Or.inr ⟨h, ⟨eK.trans e⟩⟩

theorem uc22s2112r34_g2_nonempty_equiv_sl2 {X : Type} [Group X] [Finite X] [IsSimpleGroup X]
    {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (hX : LieModel X .G2 0 p 1) {K : Subgroup X}
    (hK : IsFundamentalOver p K) : Nonempty (K ≃* SL(2, GaloisField p 1)) := by
  exact (uc22s2112r34_exc_nonempty_equiv_sl2 hp2 (Or.inl rfl) hX hK).resolve_right
    fun h => nomatch h.1

private lemma uc22s2112r34_excns_factorization_card_X {X : Type} [Group X] [Finite X]
    {t : StatedLieTag} {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (ht : t = .G2 ∨ t = .trialityD4) (hX : LieModel X t 0 p 1) :
    (Nat.card X).factorization 2 = 2 * (p ^ 2 - 1).factorization 2 := by
  have hpodd : Odd p := hp.odd_of_ne_two hp2
  have hA : p ^ 2 - 1 ≠ 0 := by
    have h := Nat.one_lt_pow (n := 2) (by norm_num) hp.one_lt
    omega
  have h6 : (p ^ 6 - 1).factorization 2 = (p ^ 2 - 1).factorization 2 :=
    uc22s2112r34_excns_factorization_pow_six_sub_one hp hp2
  have hp6m1 : p ^ 6 - 1 ≠ 0 := by
    have h := Nat.one_lt_pow (n := 6) (by norm_num) hp.one_lt
    omega
  rcases ht with rfl | rfl
  · rw [CFSG.GH74.card_of_lieModel_G2 hp2 hX, pow_one]
    unfold ordG2
    have h0 : (p ^ 6).factorization 2 = 0 :=
      uc22s2112r34_excns_factorization_pow_two hp hp2
    have hp6 : p ^ 6 ≠ 0 := pow_ne_zero _ hp.ne_zero
    rw [Nat.factorization_mul (mul_ne_zero hp6 hp6m1) hA,
      Nat.factorization_mul hp6 hp6m1]
    simp only [Finsupp.add_apply, h0, h6, zero_add]
    ring
  · rw [CFSG.GH74.card_of_lieModel_trialityD4 hp2 hX, pow_one]
    unfold ordTrialityD4
    have h0 : (p ^ 12).factorization 2 = 0 :=
      uc22s2112r34_excns_factorization_pow_two hp hp2
    have hB : (p ^ 8 + p ^ 4 + 1).factorization 2 = 0 :=
      Nat.factorization_eq_zero_of_not_dvd
        (uc22s2112r34_excns_odd_pow_eight_add hpodd).not_two_dvd_nat
    have hBne : p ^ 8 + p ^ 4 + 1 ≠ 0 := by positivity
    have hp12 : p ^ 12 ≠ 0 := pow_ne_zero _ hp.ne_zero
    rw [Nat.factorization_mul (mul_ne_zero (mul_ne_zero hp12 hBne) hp6m1) hA,
      Nat.factorization_mul (mul_ne_zero hp12 hBne) hp6m1,
      Nat.factorization_mul hp12 hBne]
    simp only [Finsupp.add_apply, h0, hB, h6, zero_add]
    ring

private lemma uc22s2112r34_excns_factorization_card_fundamental {X : Type} [Group X] [Finite X]
    [IsSimpleGroup X] {t : StatedLieTag} {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (ht : t = .G2 ∨ t = .trialityD4) (hX : LieModel X t 0 p 1) {K : Subgroup X}
    (hK : IsFundamentalOver p K) :
    (Nat.card K).factorization 2 = (p ^ 2 - 1).factorization 2 := by
  have : Fact p.Prime := ⟨hp⟩
  have hA : p ^ 2 - 1 ≠ 0 := by
    have h := Nat.one_lt_pow (n := 2) (by norm_num) hp.one_lt
    omega
  have hp6m1 : p ^ 6 - 1 ≠ 0 := by
    have h := Nat.one_lt_pow (n := 6) (by norm_num) hp.one_lt
    omega
  have hp1fac : (p ^ 1).factorization 2 = 0 :=
    uc22s2112r34_excns_factorization_pow_two hp hp2
  have hp3fac : (p ^ 3).factorization 2 = 0 :=
    uc22s2112r34_excns_factorization_pow_two hp hp2
  have h6 : (p ^ 6 - 1).factorization 2 = (p ^ 2 - 1).factorization 2 :=
    uc22s2112r34_excns_factorization_pow_six_sub_one hp hp2
  rcases uc22s2112r34_exc_nonempty_equiv_sl2 hp2 ht hX hK with h | ⟨-, h⟩
  · obtain ⟨e⟩ := h
    have hcard : Nat.card K = p ^ 1 * (p ^ 2 - 1) := by
      calc Nat.card K = Nat.card SL(2, GaloisField p 1) := Nat.card_congr e.toEquiv
        _ = Nat.card (GaloisField p 1) * (Nat.card (GaloisField p 1) ^ 2 - 1) :=
            CFSG.Quasithin.H13.KGInspOdd.card_sl2
        _ = p ^ 1 * (p ^ 2 - 1) := by
            rw [GaloisField.card p 1 (by norm_num), pow_one]
    rw [hcard, Nat.factorization_mul (pow_ne_zero _ hp.ne_zero) hA,
      Finsupp.add_apply, hp1fac, zero_add]
  · obtain ⟨e⟩ := h
    have hcard : Nat.card K = p ^ 3 * (p ^ 6 - 1) := by
      calc Nat.card K = Nat.card SL(2, GaloisField p 3) := Nat.card_congr e.toEquiv
        _ = Nat.card (GaloisField p 3) * (Nat.card (GaloisField p 3) ^ 2 - 1) :=
            CFSG.Quasithin.H13.KGInspOdd.card_sl2
        _ = p ^ 3 * (p ^ 6 - 1) := by
            rw [GaloisField.card p 3 (by norm_num)]
            have h : (p ^ 3) ^ 2 = p ^ 6 := by ring
            rw [h]
    rw [hcard, Nat.factorization_mul (pow_ne_zero _ hp.ne_zero) hp6m1,
      Finsupp.add_apply, hp3fac, zero_add, h6]

theorem uc22s2112r34_exc_exists_not_mem_sup {X : Type} [Group X] [Finite X] [IsSimpleGroup X]
    {t : StatedLieTag} {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (ht : t = .G2 ∨ t = .trialityD4)
    (hX : LieModel X t 0 p 1) (S : Sylow 2 X) {K₁ K₂ : Subgroup X}
    (hK₁ : IsFundamentalOver p K₁) (hK₂ : IsFundamentalOver p K₂) (hcomm : ⁅K₁, K₂⁆ = ⊥)
    (hC : centralizer (K₁ : Set X) ≤ K₂) : ∃ w ∈ (S : Subgroup X), w ∉ K₁ ⊔ K₂ := by
  have : Fact p.Prime := ⟨hp⟩
  by_contra h
  push Not at h
  have hSle : (S : Subgroup X) ≤ K₁ ⊔ K₂ := h
  have hScard : Nat.card S = 2 ^ (Nat.card X).factorization 2 :=
    Sylow.card_eq_multiplicity S
  have hdvdsup : 2 ^ (Nat.card X).factorization 2 ∣ Nat.card ↥(K₁ ⊔ K₂) := by
    rw [← hScard]
    exact Subgroup.card_dvd_of_le hSle
  have hcent : K₁ ≤ Subgroup.centralizer (K₂ : Set X) :=
    (Subgroup.commutator_eq_bot_iff_le_centralizer (H₁ := K₁) (H₂ := K₂)).mp hcomm
  have hnorm : K₁ ≤ Subgroup.normalizer (K₂ : Set X) :=
    hcent.trans (Subgroup.centralizer_le_normalizer (K₂ : Set X))
  have hsupmul : ((K₁ ⊔ K₂ : Subgroup X) : Set X) = (K₁ : Set X) * (K₂ : Set X) :=
    Subgroup.coe_mul_of_left_le_normalizer_right K₁ K₂ hnorm
  have hcardT : Nat.card ↥(K₁ ⊔ K₂) * Nat.card ↥(K₁ ⊓ K₂) =
      Nat.card ↥K₁ * Nat.card ↥K₂ := by
    have h := CFSG.GH74.GLS.C3.Layer1.P34.card_mul_inf K₁ K₂
    rw [← hsupmul] at h
    exact h
  have h2inf : 2 ∣ Nat.card ↥(K₁ ⊓ K₂) := by
    rcases uc22s2112r34_exc_nonempty_equiv_sl2 hp2 ht hX hK₁ with h' | ⟨-, h'⟩
    · obtain ⟨e⟩ := h'
      exact uc22s2112r34_excns_two_dvd_card_inf_of_equiv
        (CFSG.ClassicalInvolution.ModelFacts.two_ne_zero_galoisField 1 hp2) e hC
    · obtain ⟨e⟩ := h'
      exact uc22s2112r34_excns_two_dvd_card_inf_of_equiv
        (CFSG.ClassicalInvolution.ModelFacts.two_ne_zero_galoisField 3 hp2) e hC
  have hdvd : 2 ^ ((Nat.card X).factorization 2 + 1) ∣
      Nat.card ↥K₁ * Nat.card ↥K₂ := by
    rw [pow_succ, ← hcardT]
    exact mul_dvd_mul hdvdsup h2inf
  have hne₁ : Nat.card ↥K₁ ≠ 0 :=
    Nat.card_ne_zero.mpr ⟨⟨1⟩, inferInstance⟩
  have hne₂ : Nat.card ↥K₂ ≠ 0 :=
    Nat.card_ne_zero.mpr ⟨⟨1⟩, inferInstance⟩
  have hK₁fac : (Nat.card ↥K₁).factorization 2 = (p ^ 2 - 1).factorization 2 :=
    uc22s2112r34_excns_factorization_card_fundamental hp hp2 ht hX hK₁
  have hK₂fac : (Nat.card ↥K₂).factorization 2 = (p ^ 2 - 1).factorization 2 :=
    uc22s2112r34_excns_factorization_card_fundamental hp hp2 ht hX hK₂
  have hRfac : (Nat.card ↥K₁ * Nat.card ↥K₂).factorization 2 =
      2 * (p ^ 2 - 1).factorization 2 := by
    rw [Nat.factorization_mul hne₁ hne₂, Finsupp.add_apply, hK₁fac, hK₂fac]
    ring
  have hle := (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two
    (mul_ne_zero hne₁ hne₂)).mp hdvd
  rw [hRfac] at hle
  have hv := uc22s2112r34_excns_factorization_card_X hp hp2 ht hX
  rw [hv] at hle
  omega

theorem uc22s2112r34_g2_noSwapInput {X : Type} [Group X] [Finite X] [IsSimpleGroup X] {p : ℕ}
    (hp : p.Prime) (hp5 : 5 ≤ p) (hX : LieModel X .G2 0 p 1) (S : Sylow 2 X) {K₁ K₂ : Subgroup X}
    (h₁ : K₁ ∈ F14.FunSet (fundPred p) X (S : Subgroup X))
    (h₂ : K₂ ∈ F14.FunSet (fundPred p) X (S : Subgroup X)) (hcomm : ⁅K₁, K₂⁆ = ⊥)
    (hC₁ : centralizer (K₁ : Set X) ≤ K₂) (hC₂ : centralizer (K₂ : Set X) ≤ K₁) :
    UC22NoSwapInput p (S : Subgroup X) K₁ K₂ := by
  have : Fact p.Prime := ⟨hp⟩
  have hp2 : p ≠ 2 := by omega
  have hfund₁ : IsFundamentalOver p K₁ := h₁.1
  have hfund₂ : IsFundamentalOver p K₂ := h₂.1
  refine ⟨hC₁, hC₂, ?_, ?_⟩
  · intro K hK
    rcases hK with rfl | rfl
    · obtain ⟨eK⟩ := uc22s2112r34_g2_nonempty_equiv_sl2 hp2 hX hfund₁
      have hF : Nat.card (GaloisField p 1) = p := by
        rw [GaloisField.card p 1 (by norm_num), pow_one]
      refine ⟨GaloisField p 1, inferInstance, inferInstance, inferInstance,
        uc22s2112r34_rho K hp5 hF eK, ?_, fun _ => ?_⟩
      · exact uc22s2112r34_rho_eq_one_iff hp5 hF eK
      · exact uc22s2112r34_rho_not_isCyclic hp5 hF eK h₁.2
    · obtain ⟨eK⟩ := uc22s2112r34_g2_nonempty_equiv_sl2 hp2 hX hfund₂
      have hF : Nat.card (GaloisField p 1) = p := by
        rw [GaloisField.card p 1 (by norm_num), pow_one]
      refine ⟨GaloisField p 1, inferInstance, inferInstance, inferInstance,
        uc22s2112r34_rho K hp5 hF eK, ?_, fun _ => ?_⟩
      · exact uc22s2112r34_rho_eq_one_iff hp5 hF eK
      · exact uc22s2112r34_rho_not_isCyclic hp5 hF eK h₂.2
  · intro _ _ K hK
    obtain ⟨w, hwS, hw⟩ :=
      uc22s2112r34_exc_exists_not_mem_sup hp hp2 (Or.inl rfl) hX S hfund₁ hfund₂ hcomm hC₁
    exact ⟨w, hwS, uc22s2112r34_noswap_outer_of_not_mem hC₁ hC₂ hw K hK⟩

end CFSG.LocalAnalysis.UniquenessCase.UC22
