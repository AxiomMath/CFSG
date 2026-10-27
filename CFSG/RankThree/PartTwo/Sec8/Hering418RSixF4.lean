module

public import CFSG.RankThree.PartTwo.Sec8.Hering418RSix
public import CFSG.RankThree.PartTwo.Sec8.Hering418ROuter
public import CFSG.RankThree.PartTwo.Sec8.Item812Res2ProofRee
public import CFSG.RankThree.PartTwo.Sec8.Item86ResProofOrders
public import CFSG.RankThree.PartOne.RF4.FinalKFacts
public import CFSG.SignalizerFunctorTheorem.CatalogBridge.NonLocalLargeReeMain

public section

namespace CFSG.RankThree.PartTwo.Sec8.Hering418

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.AGLEmbeddingD2.Wilson.Coordinator.KF418
open CFSG.LieType.Ree

@[expose] def IsTwistedFFourSix (X : Type) [Group X] : Prop :=
  ∃ f : ℕ, 3 ∣ f ∧ Blueprint.ReeTitsModel X .twistedF4 2 f

section Outer



theorem exists_mul_pow_inn_twistedF4 {a : ℕ} (ha : 1 ≤ a) {K : Type} [Field K] [Finite K]
    [CharP K ReeTag.F4.prime] (hK : Nat.card K = 2 ^ (2 * a + 1))
    {A B : MulAut (ReeTag.F4.reeGamma K a)} (hA3 : A ^ 3 = 1) (hB3 : B ^ 3 = 1)
    (hAout : ¬ KFacts.IsInnerAut A) (hBout : ¬ KFacts.IsInnerAut B) :
    ∃ j : ℕ, KFacts.IsInnerAut (A * B ^ j) := by
  obtain ⟨σ₁, hσ₁, x₁, hx₁⟩ := KFacts.largeRee_order_three_inFieldCoset ha hK hA3 hAout
  obtain ⟨σ₂, hσ₂, x₂, hx₂⟩ := KFacts.largeRee_order_three_inFieldCoset ha hK hB3 hBout
  have hA : A = MulAut.conj x₁ * ReeTag.F4.reeGammaFieldAutHom K a σ₁ := by
    rw [ReeTag.reeGammaFieldAutHom_apply, hx₁, inv_mul_cancel_right]
  have hB : B = MulAut.conj x₂ * ReeTag.F4.reeGammaFieldAutHom K a σ₂ := by
    rw [ReeTag.reeGammaFieldAutHom_apply, hx₂, inv_mul_cancel_right]
  have h3 : σ₁ ^ 3 = 1 := by rw [← hσ₁]; exact pow_orderOf_eq_one σ₁
  have hΦ : ∀ (σ : K ≃+* K) (t : ReeTag.F4.reeGamma K a), ∃ t' : ReeTag.F4.reeGamma K a,
      ReeTag.F4.reeGammaFieldAutHom K a σ * MulAut.conj t *
        (ReeTag.F4.reeGammaFieldAutHom K a σ)⁻¹ = MulAut.conj t' :=
    fun σ t => ⟨_, KFacts.mul_mulAutConj_mul_inv _ t⟩
  obtain ⟨j, hj⟩ := exists_mul_pow_mem_range_of_normalizes
    (MulAut.conj : ReeTag.F4.reeGamma K a →* MulAut (ReeTag.F4.reeGamma K a))
    (ReeTag.F4.reeGammaFieldAutHom K a) hΦ
    (ringAut_order_three_rel Nat.prime_two (by omega : 1 ≤ 2 * a + 1) hK hσ₁ hσ₂) h3 x₁ x₂
  refine ⟨j, ?_⟩
  rw [hA, hB]
  exact hj

theorem kF418OuterOn_TwistedF4Six : KF418OuterOn (fun X _ => IsTwistedFFourSix X) := by
  intro G _ _ L hL hl a b ha3 hb3 hab hb1 habz haN hbN hbC haC K hK n hn htype hKa hbk
  obtain ⟨f, h3f, hX⟩ := hl
  obtain ⟨-, a', ha1, hfa, Kf, _, _, _, hKf, ⟨e⟩⟩ := Sec4.exists_mulEquiv_reeGamma hX
  have c := Cfg.of_model hK ha3 hb3 hab haN hbN hbC haC hKa
  have hKq := Sec6.isQuasisimple_of_mem_thetaComponentsIn hK
  have hβ : Sec4.InducesOuterTheta b L := by
    rcases hbk with h | h
    · exact KFacts.InducesStdKind.inducesOuterTheta (k := .field) L h (by decide)
    · exact KFacts.InducesStdKind.inducesOuterTheta (k := .graphField) L h (by decide)
  obtain ⟨b', k', _, _, _, hk', -, ⟨eC⟩⟩ :=
    Item812Res2.exists_barCentralizer_mulEquiv_reeGamma_index ha1 hKf e hb3 hβ
  haveI : IsSimpleGroup (ReeTag.F4.reeGamma Kf a') :=
    CFSG.SignalizerFunctorTheorem.CatalogBridge.isSimpleGroup_reeGamma_F4 ha1 hKf
  haveI : IsSimpleGroup (L ⧸ aschbacherSolvableCore 3 L) := e.isSimpleGroup
  have hZ : Subgroup.center (L ⧸ aschbacherSolvableCore 3 L) = ⊥ :=
    center_eq_bot_of_isQuasisimple_of_isSimpleGroup hL.2.2
  by_cases hb0 : b' = 0
  ·
    subst hb0
    have h7 : 7 ∣ Nat.card ((K ⧸ aschbacherSolvableCore 3 K) ⧸
        Subgroup.center (K ⧸ aschbacherSolvableCore 3 K)) := (type418Arith_of hn hKq htype).1
    have h1 := card_quot_center_dvd_card c.hKL
    have hT := c.card_rhoK_range_dvd hZ
    have hC : Nat.card (Sec8.barCentralizer (Subgroup.zpowers b) L) =
        CFSG.Open.ordTwistedF4 (2 ^ (2 * 0 + 1)) :=
      Sec8.Item86ResProof.card_of_mulEquiv_reeGamma 0 k' hk' eC
    have h := h7.trans (h1.trans hT)
    rw [hC] at h
    have hv : CFSG.Open.ordTwistedF4 (2 ^ (2 * 0 + 1)) = 35942400 := by
      simp only [CFSG.Open.ordTwistedF4]
      norm_num
    rw [hv] at h
    omega
  ·
    have hb1' : 1 ≤ b' := by omega
    haveI : IsSimpleGroup (ReeTag.F4.reeGamma k' b') :=
      CFSG.SignalizerFunctorTheorem.CatalogBridge.isSimpleGroup_reeGamma_F4 hb1' hk'
    haveI : IsSimpleGroup ↥(Sec8.barCentralizer (Subgroup.zpowers b) L) := eC.isSimpleGroup
    have hC := barCentralizer_le_imageModTheta_of_simple c.hbL hb3 hK inferInstance
      (imageModTheta_ne_bot c.hKL hKq)
    have hinn : ∃ j : ℕ, c.alpha * c.beta ^ j ∈ innBar L := by
      have hA3 : KFacts.inducedAutHom L e ⟨a, c.haL⟩ ^ 3 = 1 :=
        KFacts.inducedAutHom_pow_eq_one L e c.haL c.ha3
      have hB3 : KFacts.inducedAutHom L e ⟨b, c.hbL⟩ ^ 3 = 1 :=
        KFacts.inducedAutHom_pow_eq_one L e c.hbL c.hb3
      have hBout : ¬ KFacts.IsInnerAut (KFacts.inducedAutHom L e ⟨b, c.hbL⟩) :=
        (KFacts.not_isInnerAut_inducedAutHom_iff L e c.hbL).mpr hβ
      by_cases hAin : KFacts.IsInnerAut (KFacts.inducedAutHom L e ⟨a, c.haL⟩)
      · refine ⟨0, ?_⟩
        rw [pow_zero, mul_one]
        exact (KFacts.isInnerAut_congr e c.alpha).mp hAin
      · obtain ⟨j, hj⟩ := exists_mul_pow_inn_twistedF4 ha1 hKf hA3 hB3 hAin hBout
        refine ⟨j, ?_⟩
        have h1 : KFacts.inducedAutHom L e ⟨a, c.haL⟩ *
            KFacts.inducedAutHom L e ⟨b, c.hbL⟩ ^ j = MulAut.congr e (c.alpha * c.beta ^ j) := by
          rw [map_mul, map_pow]
          rfl
        rw [h1] at hj
        exact (KFacts.isInnerAut_congr e _).mp hj
    exact c.false_of_outer_core hZ hinn hC

theorem kF418ModelOn_TwistedF4Six_of_rank (hrank : Sec21.TwistedF4EvenThreeRankTwo) :
    KF418ModelOn (fun X _ => IsTwistedFFourSix X) := by
  refine kF418ModelOn_of_outer ?_ ?_ kF418OuterOn_TwistedF4Six
  · rintro X _ _ ⟨f, h3f, hX⟩
    exact bound_inner_of_pRank (MulEquiv.refl _) (hrank X f hX)
  · intro G _ _ L hL hl x hx3 hout
    obtain ⟨f, h3f, hX⟩ := hl
    obtain ⟨-, a, ha1, hfa, K, _, _, _, hK, ⟨e⟩⟩ := Sec4.exists_mulEquiv_reeGamma hX
    exact Or.inl (KFacts.InducesStdKind.largeRee a ha1 K hK
      (KFacts.inducesKindLargeRee_field L ha1 hK
        (CFSG.RankThree.PartOne.RF4.largeReeOrderThreeFieldConj a K hK) hx3 hout e))

end Outer

end CFSG.RankThree.PartTwo.Sec8.Hering418
