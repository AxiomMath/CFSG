module

public import CFSG.LocalAnalysis.StandardType.GGSporKOrdBMRed
public import CFSG.LieType.ChevTwo.OppCl.D4Lift
public import CFSG.HardMathSupport.Lang.Coordinator.D4Bridge.Bridge
public import CFSG.LocalAnalysis.ComponentInitial.BasicFacts
public import CFSG.LocalAnalysis.ComponentInitial.DiagonalSemilinear
public import CFSG.LocalAnalysis.StandardType.GGSporKOrdBMOut
public import CFSG.LocalAnalysis.StandardType.GGSporKOrd7G2
public import CFSG.LocalAnalysis.StandardType.GGSporKOrd7F4
public import CFSG.LocalAnalysis.StandardType.GGSporKOrd7TrialityD4
public import CFSG.LocalAnalysis.StandardType.GGSporKOrd7TwistedE6
public import CFSG.LocalAnalysis.StandardType.GGSporKOrd7Suzuki
public import CFSG.LocalAnalysis.StandardType.GGSporKOrd7Tits
public import CFSG.LieType.ChevTwo.OppositeFixedExcTri

public section

namespace CFSG.StandardType.SporadicShape

open CFSG CFSG.StandardType CFSG.Assembly CFSG.Blueprint CFSG.Open
  CFSG.EvenSmallLie.CatalogOrders

private theorem lre6bx1_subsingleton_ringAut (K : Type*) [Field K] [Finite K]
    (hK : Nat.card K = 2) : Subsingleton (K ≃+* K) := by
  have h1 : Nat.card (K ≃+* K) = 1 := by
    have h := (CFSG.LocalAnalysis.ComponentInitial.card_ringAut_and_isCyclic
      (p := 2) (n := 1) Nat.prime_two K (by rw [hK, pow_one])).1
    simpa using h
  exact (Nat.card_eq_one_iff_unique.mp h1).1

private theorem lre6bx1_card_sup_zpowers_dvd {G : Type*} [Group G]
    (C : Subgroup G) (P : G) (hPnorm : P ∈ Subgroup.normalizer (C : Set G))
    (hP3 : P ^ 3 = 1) :
    Nat.card (C ⊔ Subgroup.zpowers P : Subgroup G) ∣ 3 * Nat.card C := by
  let T : Subgroup G := Subgroup.zpowers P ⊔ C
  have hT : T = C ⊔ Subgroup.zpowers P := by
    change Subgroup.zpowers P ⊔ C = C ⊔ Subgroup.zpowers P
    rw [sup_comm]
  rw [← hT]
  have hnorm : Subgroup.zpowers P ≤ Subgroup.normalizer (C : Set G) :=
    Subgroup.zpowers_le.2 hPnorm
  have hTCnorm : T ≤ Subgroup.normalizer (C : Set G) := by
    change Subgroup.zpowers P ⊔ C ≤ Subgroup.normalizer (C : Set G)
    exact sup_le hnorm Subgroup.le_normalizer
  haveI : (C.subgroupOf T).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer hTCnorm
  have hiso : Nat.card (Subgroup.zpowers P ⧸ C.subgroupOf (Subgroup.zpowers P)) =
      Nat.card (T ⧸ C.subgroupOf T) :=
    Nat.card_congr (QuotientGroup.quotientInfEquivProdNormalizerQuotient
      (Subgroup.zpowers P) C hnorm).toEquiv
  have hq : Nat.card (Subgroup.zpowers P ⧸ C.subgroupOf (Subgroup.zpowers P)) ∣ 3 := by
    refine (Subgroup.card_quotient_dvd_card (C.subgroupOf (Subgroup.zpowers P))).trans ?_
    rw [Nat.card_zpowers]
    exact orderOf_dvd_of_pow_eq_one hP3
  have hcardT : Nat.card T =
      Nat.card (T ⧸ C.subgroupOf T) * Nat.card C := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (C.subgroupOf T)]
    congr 1
    exact Nat.card_congr
      (Subgroup.subgroupOfEquivOfLe (le_sup_right : C ≤ Subgroup.zpowers P ⊔ C)).toEquiv
  calc Nat.card T
      = Nat.card (T ⧸ C.subgroupOf T) * Nat.card C := hcardT
    _ = Nat.card (Subgroup.zpowers P ⧸ C.subgroupOf (Subgroup.zpowers P)) * Nat.card C := by
          rw [← hiso]
    _ ∣ 3 * Nat.card C := Nat.mul_dvd_mul_right hq (Nat.card C)

open CFSG.Blueprint.Chevalley CFSG.HardMathSupport.Lang.D4Three CFSG.LieType.ChevTwo.Semi in
theorem ordBMBound_D4_two :
    OrdBMBound .POmegaPlus 4 2 1 (3 * lieOrd .POmegaPlus 4 2) := by
  unfold OrdBMBound
  intro R _ _ _ hmodel ℓ hℓprime hℓ2
  rcases hmodel with ⟨-, hc⟩ | ⟨h0, -⟩ | ⟨h0, -⟩ | ⟨h0, -⟩
  · have hSc : StatedClassicalModel R .POmegaPlus 4 2 1 := hc
    dsimp only [StatedClassicalModel] at hc
    rcases hc with ⟨-, K, hKfield, hKfinite, hKcard, ⟨e⟩⟩
    letI : Field K := hKfield
    letI : Finite K := hKfinite
    have hK2 : Nat.card K = 2 := by rw [hKcard, pow_one]
    haveI : CharP K 2 :=
      CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
        (p := 2) (k := 1) Nat.prime_two (by norm_num) hKcard
    have hringChar : ringChar K = 2 := ringChar.eq K 2
    obtain ⟨e'⟩ :=
      CFSG.HardMathSupport.Lang.Coordinator.D4Bridge.nonempty_statedProj_equiv_adjointGroup K
    let C : Subgroup (ModGL Tag.D4 K) := adjointGroup Tag.D4 K
    have hcardR : Nat.card R = lieOrd .POmegaPlus 4 2 := by
      have h := card_eq_lieOrd_of_classical hSc
      rw [pow_one] at h
      exact h
    have hcardC : Nat.card C = lieOrd .POmegaPlus 4 2 :=
      (Nat.card_congr (e.trans e').toEquiv).symm.trans hcardR
    have hAutEq : Nat.card (MulAut R) = Nat.card (MulAut C) :=
      Nat.card_congr (MulAut.congr (e.trans e')).toEquiv
    haveI : Finite (ModGL Tag.D4 K) :=
      CFSG.LieType.Chevalley.finite_modGL (τ := Tag.D4) (K := K)
    haveI : Finite C := inferInstance
    haveI : Finite (MulAut C) := inferInstance
    haveI : Fact ℓ.Prime := ⟨hℓprime⟩
    haveI : Subsingleton (K ≃+* K) := lre6bx1_subsingleton_ringAut K hK2
    have hPnorm : d4P K ∈ Subgroup.normalizer (C : Set (ModGL Tag.D4 K)) := by
      simpa only [C] using d4P_mem_normalizer_adjointGroup (K := K)
    have hP3 : (d4P K) ^ 3 = 1 := d4P_pow_three (K := K)
    let T : Subgroup (ModGL Tag.D4 K) := C ⊔ Subgroup.zpowers (d4P K)
    have hTnorm : T ≤ Subgroup.normalizer (C : Set (ModGL Tag.D4 K)) := by
      change C ⊔ Subgroup.zpowers (d4P K) ≤
        Subgroup.normalizer (C : Set (ModGL Tag.D4 K))
      exact sup_le Subgroup.le_normalizer (Subgroup.zpowers_le.2 hPnorm)
    let Φ : T →* MulAut C :=
      (Subgroup.normalizerMonoidHom C).comp (Subgroup.inclusion hTnorm)
    obtain ⟨S⟩ := Sylow.nonempty (p := ℓ) (G := MulAut C)
    let Rsub : Subgroup (MulAut C) := S
    have hRsub_isP : IsPGroup ℓ Rsub := by
      simpa only [Rsub] using S.isPGroup'
    have hS_card : Nat.card Rsub = ℓ ^ (Nat.card (MulAut C)).factorization ℓ := by
      simpa only [Rsub] using Sylow.card_eq_multiplicity S
    have hS_le_range : Rsub ≤ Φ.range := by
      intro α hα
      obtain ⟨k, hk⟩ := hRsub_isP.exists_orderOf_eq_pow ⟨α, hα⟩
      have hk' : orderOf α = ℓ ^ k := by
        rw [← Subgroup.orderOf_mk α hα]
        exact hk
      have hodd : Odd (orderOf α) := by
        rw [hk']
        exact (hℓprime.odd_of_ne_two hℓ2).pow
      obtain ⟨g, σ, ε, -, hform⟩ :=
        exists_odd_normal_form (K := K) hringChar hodd (pow_orderOf_eq_one α)
      have hform' : ∀ h : C, (α h : ModGL Tag.D4 K) =
          (g : ModGL Tag.D4 K) * d4P K ^ ε * (h : ModGL Tag.D4 K) *
            ((g : ModGL Tag.D4 K) * d4P K ^ ε)⁻¹ := by
        intro h
        have hh := hform h
        have h1 : σ.toRingHom = RingHom.id K := by
          rw [Subsingleton.elim σ 1]; rfl
        rw [h1] at hh
        have h2 : Units.map (entrywiseHom (RingHom.id K)) (h : ModGL Tag.D4 K) =
            (h : ModGL Tag.D4 K) := Units.ext (CFSG.LieType.Chevalley.entrywise_id (R := K) _)
        rw [h2] at hh
        exact hh
      have hxmem : (g : ModGL Tag.D4 K) * d4P K ^ ε ∈ T :=
        Subgroup.mul_mem _
          (Subgroup.mem_sup_left g.2)
          (Subgroup.mem_sup_right (Subgroup.pow_mem _ (Subgroup.mem_zpowers (d4P K)) ε))
      refine ⟨⟨(g : ModGL Tag.D4 K) * d4P K ^ ε, hxmem⟩, ?_⟩
      apply MulEquiv.ext
      intro h
      apply Subtype.ext
      rw [hform' h]
      change ((Subgroup.normalizerMonoidHom C)
          (Subgroup.inclusion hTnorm
            ⟨(g : ModGL Tag.D4 K) * d4P K ^ ε, hxmem⟩)) h =
        (g : ModGL Tag.D4 K) * d4P K ^ ε * (h : ModGL Tag.D4 K) *
          ((g : ModGL Tag.D4 K) * d4P K ^ ε)⁻¹
      rw [Subgroup.normalizerMonoidHom_apply_apply_coe]
      rfl
    have hTdvd : Nat.card T ∣ 3 * Nat.card C := by
      simpa only [T] using lre6bx1_card_sup_zpowers_dvd C (d4P K) hPnorm hP3
    have hSdvd : Nat.card Rsub ∣ 3 * Nat.card C :=
      (Subgroup.card_dvd_of_le hS_le_range).trans
        ((Subgroup.card_range_dvd Φ).trans hTdvd)
    have hk_le : (Nat.card (MulAut C)).factorization ℓ ≤
        (3 * Nat.card C).factorization ℓ := by
      have hCne : Nat.card C ≠ 0 := Nat.card_ne_zero.mpr ⟨⟨1⟩, inferInstance⟩
      have hMne : 3 * Nat.card C ≠ 0 := mul_ne_zero (by norm_num) hCne
      rw [hS_card] at hSdvd
      exact (Nat.Prime.pow_dvd_iff_le_factorization hℓprime hMne).mp hSdvd
    rw [hAutEq, ← hcardC]
    exact hk_le
  all_goals exact absurd h0 (by norm_num)

theorem ordBMBound_G2_four :
    OrdBMBound .G2 0 2 2 (lieOrd .G2 0 4 * 2) := by
  intro R _ _ _ hmodel ℓ hℓ hℓ2
  have hce : ChevalleyExceptionalModel R .G2 2 2 :=
    hmodel.chevalleyExceptionalModel (by decide)
  have hcard : Nat.card R = lieOrd .G2 0 4 := by
    have h := card_eq_lieOrd_of_exceptional (p := 2) (f := 2) hce
    simpa using h
  have hR0 : Nat.card R ≠ 0 := by
    exact Nat.card_ne_zero.2 ⟨⟨1⟩, inferInstance⟩
  have hdvd : Nat.card (MulAut R) ∣ lieOrd .G2 0 4 * 2 := by
    have h := ord7_card_mulAut_dvd_G2 (f := 2) hmodel
    rw [mul_comm (lieOrd .G2 0 4) 2, ← hcard]
    exact h
  exact bmFact_le_of_dvd (by rw [← hcard]; exact mul_ne_zero hR0 (by norm_num)) hdvd ℓ

theorem ordBMBound_F4_two :
    OrdBMBound .F4 0 2 1 (lieOrd .F4 0 2 * 2) := by
  intro R _ _ _ hmodel ℓ hℓ hℓ2
  have hce : ChevalleyExceptionalModel R .F4 2 1 :=
    hmodel.chevalleyExceptionalModel (by decide)
  have hcard : Nat.card R = lieOrd .F4 0 2 := by
    have h := card_eq_lieOrd_of_exceptional (p := 2) (f := 1) hce
    simpa using h
  have hR0 : Nat.card R ≠ 0 := by
    exact Nat.card_ne_zero.2 ⟨⟨1⟩, inferInstance⟩
  have hdvd : Nat.card (MulAut R) ∣ lieOrd .F4 0 2 * 2 := by
    have h := ord7_card_mulAut_dvd_F4 (f := 1) hmodel
    rw [mul_comm (lieOrd .F4 0 2) 2, ← hcard]
    simpa using h
  exact bmFact_le_of_dvd (by rw [← hcard]; exact mul_ne_zero hR0 (by norm_num)) hdvd ℓ

theorem ordBMBound_trialityD4_two :
    OrdBMBound .trialityD4 0 2 1 (lieOrd .trialityD4 0 2 * 3) := by
  intro R _ _ _ hmodel ℓ hℓ hℓ2
  have hce : ChevalleyExceptionalModel R .trialityD4 2 1 :=
    hmodel.chevalleyExceptionalModel (by decide)
  have hcard : Nat.card R = lieOrd .trialityD4 0 2 := by
    have h := card_eq_lieOrd_of_exceptional (p := 2) (f := 1) hce
    simpa using h
  have hR0 : Nat.card R ≠ 0 := by
    exact Nat.card_ne_zero.2 ⟨⟨1⟩, inferInstance⟩
  have hdvd : Nat.card (MulAut R) ∣ lieOrd .trialityD4 0 2 * 3 := by
    have h := ord7_card_mulAut_dvd_trialityD4 (f := 1) hmodel
    rw [mul_comm (lieOrd .trialityD4 0 2) 3, ← hcard]
    simpa using h
  exact bmFact_le_of_dvd (by rw [← hcard]; exact mul_ne_zero hR0 (by norm_num)) hdvd ℓ

theorem ordBMBound_twistedE6_two :
    OrdBMBound .twistedE6 0 2 1 (lieOrd .twistedE6 0 2 * 18) := by
  intro R _ _ _ hmodel ℓ _hℓ _hℓ2
  have hcard : Nat.card R = lieOrd .twistedE6 0 2 := by
    simpa using
      (CFSG.EvenSmallLie.CatalogOrders.card_eq_lieOrd_of_exceptional
        (CFSG.Blueprint.LieModel.chevalleyExceptionalModel hmodel (by decide)))
  have hAut : Nat.card (MulAut R) ∣ 18 * Nat.card R :=
    ord7_card_mulAut_dvd_twistedE6_two hmodel
  have hl0 : lieOrd .twistedE6 0 2 ≠ 0 := by
    rw [← hcard]; exact Nat.card_pos.ne'
  have hB : lieOrd .twistedE6 0 2 * 18 ≠ 0 := mul_ne_zero hl0 (by norm_num)
  have hdvd : Nat.card (MulAut R) ∣ lieOrd .twistedE6 0 2 * 18 := by
    rw [mul_comm, ← hcard]; exact hAut
  exact bmFact_le_of_dvd hB hdvd ℓ

theorem ordBMBound_twistedB2 {f : ℕ} (hf : f = 3 ∨ f = 5) :
    OrdBMBound .twistedB2 0 2 f (lieOrd .twistedB2 0 (2 ^ f) * f) := by
  intro R _ _ _ hmodel ℓ _hℓ _hℓ2
  have hsz : SuzukiModel R 2 f := by
    rcases hmodel with ⟨ht, -⟩ | ⟨-, ht, -⟩ | ⟨-, ht, -⟩ | ⟨-, -, hsz⟩
    · exact absurd ht (by decide)
    · exact absurd ht (by decide)
    · exact absurd ht (by decide)
    · exact hsz
  have hcard : Nat.card R = lieOrd .twistedB2 0 (2 ^ f) :=
    (CFSG.EvenSmallLie.CatalogOrders.card_eq_lieOrd_of_suzuki hsz).2.2
  have hAut : Nat.card (MulAut R) ∣ f * Nat.card R :=
    ord7_card_mulAut_dvd_twistedB2 hmodel
  have hl0 : lieOrd .twistedB2 0 (2 ^ f) ≠ 0 := by
    rw [← hcard]; exact Nat.card_pos.ne'
  have hf0 : f ≠ 0 := by rcases hf with h | h <;> omega
  have hB : lieOrd .twistedB2 0 (2 ^ f) * f ≠ 0 := mul_ne_zero hl0 hf0
  have hdvd : Nat.card (MulAut R) ∣ lieOrd .twistedB2 0 (2 ^ f) * f := by
    rw [mul_comm, ← hcard]; exact hAut
  exact bmFact_le_of_dvd hB hdvd ℓ

theorem ordBMBound_Tits :
    OrdBMBound .Tits 0 2 1 (2 * CFSG.Open.ordTits) := by
  intro R _ _ _ hmodel ℓ _hℓ _hℓ2
  have hrt : ReeTitsModel R .Tits 2 1 :=
    (CFSG.Blueprint.LieModel.reeTitsModel hmodel (by decide)).2
  have hcard : Nat.card R = CFSG.Open.ordTits :=
    CFSG.SeitzReduction.F4Pilot.EvenExc.card_of_reeTitsModel_tits hrt
  have hAut : Nat.card (MulAut R) ∣ 2 * Nat.card R :=
    ord7_card_mulAut_dvd_Tits hmodel
  have hl0 : CFSG.Open.ordTits ≠ 0 := by
    rw [← hcard]; exact Nat.card_pos.ne'
  have hB : 2 * CFSG.Open.ordTits ≠ 0 := mul_ne_zero (by norm_num) hl0
  have hdvd : Nat.card (MulAut R) ∣ 2 * CFSG.Open.ordTits := by
    rw [← hcard]; exact hAut
  exact bmFact_le_of_dvd hB hdvd ℓ

end CFSG.StandardType.SporadicShape
