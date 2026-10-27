module

public import CFSG.LocalAnalysis.SeitzReduction.TwistedE6PilotQ2FieldUnique
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotCatTypeDet
public import CFSG.LocalAnalysis.SeitzReduction.TwistedE6PilotQ2BLift
public import CFSG.LocalAnalysis.SeitzReduction.TwistedE6PilotQ2Main

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.TwistedE6Pilot

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.EvenSmallLie CFSG.LieType.Chevalley.E6GraphLevi
open CFSG.Quasithin (perfectCore)
open CFSG.SeitzReduction.F4Pilot (centralizerPerfectCore)
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.SeitzReduction.UnitaryPilot (SUmOvergroup)


@[expose] def TwistedE6TwoFieldModelInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G) (k K : Type) [Field k] [Field K]
    [Algebra k K], SeitzSetting G L → Nat.card k = 2 ^ 1 → Nat.card K = (2 ^ 1) ^ 2 →
    ∀ (σ : K →+* K), (∀ c, σ c = c ^ 2 ^ 1) →
    ∀ (e : L ≃* graphFixedRootGroup TwistTag.E6 K σ) (t : G), t ∈ centralizer (L : Set G) →
      orderOf t = 2 →
      ∀ A : Subgroup (ModGL TwistTag.E6.tag K), A ≤ thetaRankOneGroup (algebraMap k K) →
        Nat.card A = 2 ^ 1 + 1 → IsCyclic A →
        ∀ htX : t ∈ centralizer (modelToG e A : Set G),
        ∀ Kc : Subgroup (centralizer (modelToG e A : Set G) ⧸
          oddCore (centralizer (modelToG e A : Set G))), IsComponent Kc →
        Kc.map (MulAut.conj (QuotientGroup.mk' (oddCore (centralizer (modelToG e A : Set G)))
          ⟨t, htX⟩)).toMonoidHom = Kc →
        ((modelToG e (su6Levi σ)).subgroupOf (centralizer (modelToG e A : Set G))).map
          (QuotientGroup.mk' (oddCore (centralizer (modelToG e A : Set G)))) < Kc →
        QuotientGroup.mk' (oddCore (centralizer (modelToG e A : Set G))) ⟨t, htX⟩ ∉ Kc →
        ∀ hsN : QuotientGroup.mk' (oddCore (centralizer (modelToG e A : Set G))) ⟨t, htX⟩ ∈
          normalizer (Kc : Set (centralizer (modelToG e A : Set G) ⧸
            oddCore (centralizer (modelToG e A : Set G)))),
        SUmOvergroup Kc (Kc.normalizerMonoidHom ⟨_, hsN⟩) 6 1 →
        ∃ G₀ : Subgroup G, ⁅G₀, G₀⁆ = G₀ ∧ Odd (Nat.card (center G₀)) ∧
          Nonempty (G₀ ⧸ center G₀ ≃* adjointGroup .E6 K) ∧ t ∈ normalizer (G₀ : Set G) ∧
          centralizerPerfectCore (modelToG e A) ≤ G₀

@[expose] def TwistedE6TwoFieldCTInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G) (k K : Type) [Field k] [Field K]
    [Algebra k K], SeitzSetting G L → Nat.card k = 2 ^ 1 → ∀ hK : Nat.card K = (2 ^ 1) ^ 2,
    ∀ (σ : K →+* K), (∀ c, σ c = c ^ 2 ^ 1) →
    ∀ (e : L ≃* graphFixedRootGroup TwistTag.E6 K σ) (t : G), t ∈ centralizer (L : Set G) →
      orderOf t = 2 →
      ∀ A : Subgroup (ModGL TwistTag.E6.tag K), A ≤ thetaRankOneGroup (algebraMap k K) →
        Nat.card A = 2 ^ 1 + 1 → IsCyclic A →
        FieldCoverParamX σ (E6GraphLevi.two_eq_zero_of_card_sq le_rfl hK) e t (modelToG e A) →
        ∃ G₀ : Subgroup G, ⁅G₀, G₀⁆ = G₀ ∧ Odd (Nat.card (center G₀)) ∧
          Nonempty (G₀ ⧸ center G₀ ≃* adjointGroup .E6 K) ∧ t ∈ normalizer (G₀ : Set G) ∧
          centralizerPerfectCore (modelToG e A) ≤ G₀

theorem twistedE6TwoFieldRowInput_of_modelInput (h : TwistedE6TwoFieldModelInput) :
    TwistedE6TwoFieldRowInput := by
  intro G _ _ L k K _ _ _ hset hk hK σ hσ e t htC ht A hAJ hA hcyc htX Kc hKc hKt hDK htK hsN hov
  obtain ⟨G₀, hG₀p, hZ, ⟨Ψ⟩, htN, hX⟩ :=
    h G L k K hset hk hK σ hσ e t htC ht A hAJ hA hcyc htX Kc hKc hKt hDK htK hsN hov
  exact false_of_fieldModel_twistedE6_two hset hk hK hσ e htC ht hAJ hG₀p hZ Ψ htN hX

section Cover


variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {k K : Type} [Field k] [Field K]
  [Algebra k K]

theorem nonempty_a5Levi_mulEquiv_of_sumOvergroup_two (hk : Nat.card k = 2 ^ 1)
    (hK : Nat.card K = (2 ^ 1) ^ 2) {σ : K →+* K} (hσ : ∀ c, σ c = c ^ 2 ^ 1) {X : Subgroup G}
    {Kc : Subgroup (centralizer (X : Set G) ⧸ oddCore (centralizer (X : Set G)))}
    (hKc : IsComponent Kc) {τ : MulAut Kc} (hov : SUmOvergroup Kc τ 6 1) :
    center Kc = ⊥ ∧ Nonempty (subsystemGroup TwistTag.E6.tag K E6GraphLevi.setA ≃* Kc) := by
  have hZ : center Kc = ⊥ := E6Pilot.center_eq_bot_of_isComponent_of_odd
    (F4Pilot.pPrimeCore_two_quotient_oddCore_eq_bot _) hKc hov.2.1
  have hlist : LieModel (Kc ⧸ center Kc) .PSL 6 2 (2 * 1) :=
    hov.2.2.resolve_right (UnitaryPilot.not_sumSmall_of_ne (six_ne_four_one 1))
  have hlist' : LieModel Kc .PSL 6 2 (2 * 1) := CFSG.LieType.CurtisTits.lieModel_of_mulEquiv
    ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot) hlist
  obtain ⟨F, _, _, hF, ⟨eK⟩⟩ := LinearPilot.exists_projectiveSL_equiv_of_lieModel_PSL hlist'
  exact ⟨hZ, nonempty_a5Levi_mulEquiv_of_projectiveSL le_rfl hk hK hσ hF eK⟩

theorem nonempty_fieldCoverParamX_2E6_nonsplit_two (hR : TwistedE6TwoDiagonalRigidity)
    (hset : SeitzSetting G L) (hk : Nat.card k = 2 ^ 1) (hK : Nat.card K = (2 ^ 1) ^ 2)
    {σ : K →+* K} (hσ : ∀ c, σ c = c ^ 2 ^ 1) (e : L ≃* graphFixedRootGroup TwistTag.E6 K σ)
    {t : G} (htC : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2)
    {A : Subgroup (ModGL TwistTag.E6.tag K)} (hAJ : A ≤ thetaRankOneGroup (algebraMap k K))
    (hA : Nat.card A = 2 ^ 1 + 1) (hcyc : IsCyclic A)
    (htX : t ∈ centralizer (modelToG e A : Set G))
    {Kc : Subgroup (centralizer (modelToG e A : Set G) ⧸
      oddCore (centralizer (modelToG e A : Set G)))} (hKc : IsComponent Kc)
    (hDK : ((modelToG e (su6Levi σ)).subgroupOf (centralizer (modelToG e A : Set G))).map
      (QuotientGroup.mk' (oddCore (centralizer (modelToG e A : Set G)))) ≤ Kc)
    (hsN : QuotientGroup.mk' (oddCore (centralizer (modelToG e A : Set G))) ⟨t, htX⟩ ∈
      normalizer (Kc : Set (centralizer (modelToG e A : Set G) ⧸
        oddCore (centralizer (modelToG e A : Set G)))))
    (hov : SUmOvergroup Kc (Kc.normalizerMonoidHom ⟨_, hsN⟩) 6 1) :
    Nonempty (FieldCoverParamX σ (E6GraphLevi.two_eq_zero_of_card_sq le_rfl hK) e t
      (modelToG e A)) := by
  have hf : 1 ≤ 1 := le_rfl
  obtain ⟨-, -, hDXc, hDq, -, -⟩ := neighbour_data_2E6_nonsplit_two hset hk hK hσ e hAJ hA hcyc
  obtain ⟨hcomp, hsyl, -⟩ :=
    neighbour_standard_2E6_nonsplit_two hset hk hK hσ e htC ht hAJ hA hcyc rfl htX rfl
  obtain ⟨hD, hDq'⟩ := neighbour_layer_2E6_nonsplit_two hk hK hσ e hAJ hA hcyc rfl rfl
  have hlist : LieModel (Kc ⧸ center Kc) .PSL 6 2 (2 * 1) :=
    hov.2.2.resolve_right (UnitaryPilot.not_sumSmall_of_ne (six_ne_four_one 1))
  have hOut := F4Pilot.isSolvable_outer_of_lieModel_PSL_quotient hKc.1.1 (by norm_num) hlist
  obtain ⟨-, -, q, hq, hqker, -, hqapp⟩ := OmegaPilot.exists_surjective_neighbourCore_of_field htC ht
    (CFSG.EvenSmallLie.centralizer_le_normalizer_of_standard hset.standardSetting.standard htC ht)
    htX hD hDq' (forall_odd_mem_2E6_nonsplit_two hR hset hk hK hσ e htC ht hAJ hA hcyc rfl rfl)
    hsyl hKc hDK hsN hov.1 hOut
  obtain ⟨-, hψ⟩ := nonempty_a5Levi_mulEquiv_of_sumOvergroup_two hk hK hσ hKc hov
  have hmemD : ∀ y : graphFixedRootGroup TwistTag.E6 K σ,
      (y : ModGL TwistTag.E6.tag K) ∈ su6Levi σ → ((e.symm y : L) : G) ∈ modelToG e (su6Levi σ) :=
    fun y hy => symm_mem_modelToG e hy
  have hDE : modelToG e (su6Levi σ) ≤ centralizerPerfectCore (modelToG e A) :=
    CFSG.Quasithin.le_perfectCore_of_perfect hDXc (Subgroup.isPerfect_iff.mp hDq.1)
  have hDE' : ∀ y : graphFixedRootGroup TwistTag.E6 K σ,
      (y : ModGL TwistTag.E6.tag K) ∈ su6Levi σ →
        ((e.symm y : L) : G) ∈ centralizerPerfectCore (modelToG e A) :=
    fun y hy => hDE (hmemD y hy)
  have hDt : modelToG e (su6Levi σ) ≤ centralizer ({t} : Set G) := fun d hd =>
    mem_centralizer_singleton_iff.2 (mem_centralizer_iff.1 htC d (modelToG_le e _ hd))
  have hDs := hcomp.1
  have hDc := (CFSG.LocalAnalysis.ComponentInitial.isComponentOf_iff_isComponent_subgroupOf hDs).1
    ((CFSG.ComponentClassification.AssemblyBPredicates.isComponentOf_iff_open _ _).2 hcomp)
  have hDcomp := F4Pilot.isComponent_subgroupOf_subgroupOf
    (F4Pilot.map_fixedSubgroup_normalizerMonoidHom Kc hsN)
    (CFSG.SeitzReduction.CentralizerComponents.isComponent_subgroupOf_inf_centralizer hDs hDc hDK)
  obtain ⟨Ψ, hΨ1, hΨ3⟩ := exists_normalized_a5Levi_mulEquiv_of_comp (G := G) hf hk hK hσ e htX
    ht rfl hDXc hDt hDK hsN hDcomp hψ (involutionDescentComp_a5Levi hf hk hK hσ)
    (autExtensionComm_a5Levi hf hk hK hσ)
  exact nonempty_fieldCoverParamX_of_normalized hf hK hσ _ e htX hDE' hsN hq hqker hqapp Ψ
    (fun y hy => hΨ1 y hy _) hΨ3

end Cover

section Final


theorem twistedE6TwoFieldModelInput_of_CT (hR : TwistedE6TwoDiagonalRigidity)
    (hCT : TwistedE6TwoFieldCTInput) : TwistedE6TwoFieldModelInput := by
  intro G _ _ L k K _ _ _ hset hk hK σ hσ e t htC ht A hAJ hA hcyc htX Kc hKc hKt hDK htK hsN hov
  obtain ⟨Φ⟩ := nonempty_fieldCoverParamX_2E6_nonsplit_two hR hset hk hK hσ e htC ht hAJ hA hcyc
    htX hKc hDK.le hsN hov
  exact hCT G L k K hset hk hK σ hσ e t htC ht A hAJ hA hcyc Φ

theorem twistedE6TwoFieldRowInput_of_CT (hR : TwistedE6TwoDiagonalRigidity)
    (hCT : TwistedE6TwoFieldCTInput) : TwistedE6TwoFieldRowInput :=
  twistedE6TwoFieldRowInput_of_modelInput (twistedE6TwoFieldModelInput_of_CT hR hCT)

end Final

end CFSG.SeitzReduction.TwistedE6Pilot
