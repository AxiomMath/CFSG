module

public import CFSG.LocalAnalysis.WeakClosure81.W16LSixCLift
public import CFSG.LocalAnalysis.WeakClosure81.W16LSixCCent
public import CFSG.LocalAnalysis.WeakClosure81.W16LSixCOne
public import CFSG.LocalAnalysis.WeakClosure81.W16LSixBFinal
public import CFSG.LocalAnalysis.WeakClosure81.W16LCPair
public import CFSG.LocalAnalysis.WeakClosure81.W16LCBig
public import CFSG.LocalAnalysis.WeakClosure81.W16LCOne
public import CFSG.LocalAnalysis.WeakClosure81.W16LCOneB
public import CFSG.LocalAnalysis.WeakClosure81.SevenKUnitaryHolds
public import CFSG.LocalAnalysis.WeakClosure81.EightFiveRootRankL2Holds
import CFSG.CGT.Timmesfeld75.Sec4CaseIIIRel
public import CFSG.LocalAnalysis.WeakClosure81.EightFiveGapFiveBridge
public import CFSG.LocalAnalysis.WeakClosure81.EightFiveGapThreeTwo
public import CFSG.LocalAnalysis.WeakClosure81.EightFiveTwoSplitMain
public import CFSG.LocalAnalysis.WeakClosure81.EightFiveU3Aut
public import CFSG.LocalAnalysis.WeakClosure81.EightTailPThreeFirst
public import CFSG.LocalAnalysis.WeakClosure81.GapTwoTransport

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.UC22 CFSG.SignalizerFunctorTheorem.Quadratic
open CFSG.Quasithin.G11
open Subgroup
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G] {M V₀ V U S H : Subgroup G}

private theorem w16l_noncomm_of_barSub {K : Subgroup G} {X : Type} [Group X] (φ : ↥K →* X)
    (g : ↥K)
    (hnc : ∃ a ∈ SevenK.barSub K φ V, ∃ b ∈ (SevenK.barSub K φ V).map
      (MulAut.conj (φ g)).toMonoidHom, a * b ≠ b * a) :
    ¬ ∀ x ∈ V, ∀ y ∈ CFSG.Quasithin.conjSubgroup V (g : G), x * y = y * x := by
  intro hall
  obtain ⟨a, ha, b, hb, hab⟩ := hnc
  obtain ⟨⟨x, hxK⟩, hxV, rfl⟩ := Subgroup.mem_map.1 ha
  obtain ⟨b', hb', rfl⟩ := Subgroup.mem_map.1 hb
  obtain ⟨⟨v, hvK⟩, hvV, rfl⟩ := Subgroup.mem_map.1 hb'
  have hxV' : x ∈ V := Subgroup.mem_subgroupOf.1 hxV
  have hvV' : v ∈ V := Subgroup.mem_subgroupOf.1 hvV
  have h1 : (g : G)⁻¹ * x * (g : G) ∈ CFSG.Quasithin.conjSubgroup V (g : G) := by
    rw [CFSG.Quasithin.mem_conjSubgroup_iff]
    simpa [mul_assoc] using hxV'
  have h2 := hall v hvV' ((g : G)⁻¹ * x * (g : G)) h1
  have key : x * ((g : G) * v * (g : G)⁻¹) = ((g : G) * v * (g : G)⁻¹) * x := by
    have h3 : (g : G) * (v * ((g : G)⁻¹ * x * (g : G))) * (g : G)⁻¹ =
        (g : G) * (((g : G)⁻¹ * x * (g : G)) * v) * (g : G)⁻¹ := by rw [h2]
    have h4 : ((g : G) * v * (g : G)⁻¹) * x = x * ((g : G) * v * (g : G)⁻¹) :=
      calc ((g : G) * v * (g : G)⁻¹) * x
          = (g : G) * (v * ((g : G)⁻¹ * x * (g : G))) * (g : G)⁻¹ := by group
        _ = (g : G) * (((g : G)⁻¹ * x * (g : G)) * v) * (g : G)⁻¹ := h3
        _ = x * ((g : G) * v * (g : G)⁻¹) := by group
    exact h4.symm
  apply hab
  have hsub : (⟨x, hxK⟩ : ↥K) * (g * ⟨v, hvK⟩ * g⁻¹) = (g * ⟨v, hvK⟩ * g⁻¹) * ⟨x, hxK⟩ :=
    Subtype.ext key
  have hφ := congrArg φ hsub
  simpa [MulAut.conj_apply, map_mul, map_inv] using hφ

private theorem w16l_zpowers_of_card_two {X : Type} [Group X] {A : Subgroup X}
    (hcard : Nat.card A = 2) (hne : A ≠ ⊥) :
    ∃ t : X, t ∈ A ∧ t ≠ 1 ∧ A = Subgroup.zpowers t := by
  obtain ⟨⟨t, htA⟩, ht1'⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hne
  have ht1 : t ≠ 1 := fun h' => ht1' (Subtype.ext h')
  refine ⟨t, htA, ht1, le_antisymm (fun a ha => ?_) (Subgroup.zpowers_le.2 htA)⟩
  by_cases ha1 : a = 1
  · rw [ha1]; exact Subgroup.one_mem _
  · rw [CFSG.CGT.Timmesfeld75.eq_of_card_two_subgroup hcard ha htA ha1 ht1]
    exact Subgroup.mem_zpowers t

private theorem w16l_normalClosure_singleton {X : Type} [Group X] {A : Subgroup X} {t : X}
    (hAt : A = Subgroup.zpowers t) (hgen : Subgroup.normalClosure (A : Set X) = ⊤) :
    Subgroup.normalClosure ({t} : Set X) = ⊤ := by
  have ht : t ∈ Subgroup.normalClosure ({t} : Set X) :=
    Subgroup.subset_normalClosure (Set.mem_singleton t)
  rw [eq_top_iff, ← hgen]
  refine Subgroup.normalClosure_le_normal fun a ha => ?_
  rw [hAt] at ha
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 ha
  exact Subgroup.zpow_mem _ ht k

section Certified


theorem IsMinFam16.liftShape_many (h1 : W16One G) (h5 : W16Five G) (hS : Std15 G)
    (h : Cex16 M V₀ V U S) (hH : IsMinFam16 M U S H) (hV : ¬ V ≤ pCoreOf 2 H)
    (D : ModDataE H (iSub16 V H)) {X : Type} [Group X]
    {φ : ↥(CFSG.Quasithin.conjClosure V H) →* X}
    (hφ : SevenK.IsBarMap (CFSG.Quasithin.conjClosure V H) (iSub16 V H) φ)
    (hShape : HatShape166 (hatX D V) (hatS D V) (E3.mQuot V (iSub16 V H)))
    (hn : 1 < E3.mQuot V (iSub16 V H)) :
    Shape166 X (SevenK.barSub (CFSG.Quasithin.conjClosure V H) φ V) (E3.mQuot V (iSub16 V H)) ∧
      ∀ N : Subgroup X, N.Normal → IsPGroup 2 N → N = ⊥ := by
  classical
  haveI : Finite X := Finite.of_surjective φ hφ.surjective
  obtain ⟨ρ, hρ⟩ := IsMinFam16.exists_barRep h1 h5 hS h hH hV D hφ
  obtain ⟨θ, hθ, hθsurj, hθA⟩ := IsMinFam16.exists_barTheta h1 h5 hS h hH hV D hφ
  have hLift := IsMinFam16.liftHyp h1 h5 hS h hH hV D hφ hρ
  obtain ⟨-, hker⟩ := IsMinFam16.ker_barTheta_central h1 h5 hS h hH hV D hφ hρ hθ
  obtain ⟨hgenA, -⟩ := IsMinFam16.normalClosure_barSub h1 hS h hH hV hφ
  have hsit := IsMinFam16.barSituation_hat h1 h5 hS h hH hV D
  have hcard : Nat.card (SevenK.barSub (CFSG.Quasithin.conjClosure V H) φ V) =
      2 ^ E3.mQuot V (iSub16 V H) := by
    rw [card_barSub_eq_relIndex_of_isBarMap (CFSG.Quasithin.le_conjClosure V H)
      (iSub16_le_conjClosure V H) hφ]
    exact E3.relIndex_eq_two_pow (B2F.isPGroup_of_isElemAbelian h.hyp.h6.elemAbelian) _
  have hBne : hatS D V ≠ ⊥ := by
    intro hbot
    have h0 := hShape.1
    rw [hbot, Subgroup.card_bot] at h0
    exact absurd (Nat.pow_eq_one.1 h0.symm) (by omega)
  have hcore : ∀ N : Subgroup (hatX D V), N.Normal → IsPGroup 2 N → N = ⊥ := by
    intro N hN hN2
    rw [eq_bot_iff, ← hsit.pCore_eq_bot]
    exact le_sSup ⟨hN, hN2⟩
  obtain ⟨l, a, ha, b, hb, hab⟩ := w16l_exists_noncomm_conj θ hθsurj hθA hBne hsit.elemAbelian
    hsit.normalClosure_eq_top hcore
  obtain ⟨g, rfl⟩ := hφ.surjective l
  have hncG := w16l_noncomm_of_barSub φ g ⟨a, ha, b, hb, hab⟩
  obtain ⟨he, he'⟩ := IsMinFam16.he_of_noncomm h1 h5 hS h hH hV D hφ hρ g hncG
  obtain ⟨n', hn'card, hpair⟩ := LiftHyp.pair_shape hLift (φ g) ⟨a, ha, b, hb, hab⟩ he he'
  have hn'n : n' = E3.mQuot V (iSub16 V H) :=
    Nat.pow_right_injective (le_refl 2) (hn'card.symm.trans hcard)
  rw [hn'n] at hpair
  have hJ : CFSG.LocalAnalysis.UniquenessCase.UC22.IsL2
        ↥(SevenK.barSub (CFSG.Quasithin.conjClosure V H) φ V ⊔
          (SevenK.barSub (CFSG.Quasithin.conjClosure V H) φ V).map
            (MulAut.conj (φ g)).toMonoidHom) (E3.mQuot V (iSub16 V H)) ∨
      CFSG.LocalAnalysis.UniquenessCase.UC22.IsSz
        ↥(SevenK.barSub (CFSG.Quasithin.conjClosure V H) φ V ⊔
          (SevenK.barSub (CFSG.Quasithin.conjClosure V H) φ V).map
            (MulAut.conj (φ g)).toMonoidHom) (E3.mQuot V (iSub16 V H)) := by
    rcases hpair with h' | h' | ⟨h1', -⟩
    · exact Or.inl h'
    · exact Or.inr h'
    · exact absurd h1' (by omega)
  let ψ : X →* hatX D V ⧸ Subgroup.center (hatX D V) :=
    (QuotientGroup.mk' (Subgroup.center (hatX D V))).comp θ
  have hψ : Function.Surjective ψ := (QuotientGroup.mk'_surjective _).comp hθsurj
  rcases hShape.2 with ⟨-, hS₀⟩ | ⟨hn1, -⟩
  · rcases hS₀ with hSp | hSz | hU3
    · obtain ⟨hL, hO⟩ := w16l_lift_L2 hn ψ hψ hker hSp hcard hgenA hJ
      exact ⟨⟨hcard, Or.inl ⟨hn, Or.inl hL⟩⟩, hO⟩
    · obtain ⟨hL, hO⟩ := w16l_lift_Sz hn ψ hψ hker hSz hcard hgenA hJ
      exact ⟨⟨hcard, Or.inl ⟨hn, Or.inr (Or.inl hL)⟩⟩, hO⟩
    · obtain ⟨hL, hO⟩ := w16l_lift_U3 hn ψ hψ hker hU3 hcard hgenA hJ
      exact ⟨⟨hcard, Or.inl ⟨hn, Or.inr (Or.inr hL)⟩⟩, hO⟩
  · exact absurd hn1 (by omega)

theorem IsMinFam16.liftShape_one (h1 : W16One G) (h5 : W16Five G) (hS : Std15 G)
    (h : Cex16 M V₀ V U S) (hH : IsMinFam16 M U S H) (hV : ¬ V ≤ pCoreOf 2 H)
    (D : ModDataE H (iSub16 V H)) {X : Type} [Group X]
    {φ : ↥(CFSG.Quasithin.conjClosure V H) →* X}
    (hφ : SevenK.IsBarMap (CFSG.Quasithin.conjClosure V H) (iSub16 V H) φ)
    (hShape : HatShape166 (hatX D V) (hatS D V) (E3.mQuot V (iSub16 V H)))
    (hn : E3.mQuot V (iSub16 V H) = 1) :
    Shape166 X (SevenK.barSub (CFSG.Quasithin.conjClosure V H) φ V) (E3.mQuot V (iSub16 V H)) ∧
      ∀ N : Subgroup X, N.Normal → IsPGroup 2 N → N = ⊥ := by
  classical
  haveI : Finite X := Finite.of_surjective φ hφ.surjective
  obtain ⟨ρ, hρ⟩ := IsMinFam16.exists_barRep h1 h5 hS h hH hV D hφ
  obtain ⟨θ, hθ, hθsurj, hθA⟩ := IsMinFam16.exists_barTheta h1 h5 hS h hH hV D hφ
  have hLift := IsMinFam16.liftHyp h1 h5 hS h hH hV D hφ hρ
  obtain ⟨hker1, -⟩ := IsMinFam16.ker_barTheta_central h1 h5 hS h hH hV D hφ hρ hθ
  obtain ⟨hgenA, -⟩ := IsMinFam16.normalClosure_barSub h1 hS h hH hV hφ
  have hcard0 : Nat.card (SevenK.barSub (CFSG.Quasithin.conjClosure V H) φ V) =
      2 ^ E3.mQuot V (iSub16 V H) := by
    rw [card_barSub_eq_relIndex_of_isBarMap (CFSG.Quasithin.le_conjClosure V H)
      (iSub16_le_conjClosure V H) hφ]
    exact E3.relIndex_eq_two_pow (B2F.isPGroup_of_isElemAbelian h.hyp.h6.elemAbelian) _
  have hcard2 : Nat.card (SevenK.barSub (CFSG.Quasithin.conjClosure V H) φ V) = 2 := by
    rw [hcard0, hn]; norm_num
  obtain ⟨t, htA, ht1, hAt⟩ := w16l_zpowers_of_card_two hcard2 hLift.ne_bot_A
  have ht2 : t * t = 1 := by
    have := hLift.elemAbelian.2 t htA
    simpa [pow_two] using this
  have hnc : Subgroup.normalClosure ({t} : Set X) = ⊤ := w16l_normalClosure_singleton hAt hgenA
  have hO2 : ∀ N : Subgroup X, N.Normal → IsPGroup 2 N → N ⊓ Subgroup.zpowers t = ⊥ := by
    intro N hN hN2
    have := (IsMinFam16.pCore_le_center_bar h1 h5 hS h hH hV hφ N hN hN2).2
    rwa [hAt] at this
  have hne : Subgroup.zpowers t ≠ ⊤ := by
    rw [← hAt]
    exact IsMinFam16.barSub_ne_top h1 h5 hS h hH hV hφ
  rcases hShape.2 with ⟨hn1, -⟩ | ⟨-, hOdd⟩
  · exact absurd hn1 (by omega)
  have hX : Subgroup.zpowers (θ t) ⊔ fusionOddCore (hatX D V) = ⊤ := by
    rw [← MonoidHom.map_zpowers, ← hAt, hθA]
    exact hOdd
  obtain ⟨hE, hcore, hOne, hgen⟩ := w16l_one_structure ht2 ht1 hnc hO2 hne θ hθsurj hker1 hX
  obtain ⟨hTr, hTI⟩ := w16l_traceSpace_ti hLift hAt hcard2
  have hexp := IsMinFam16.exp_class_oddCore h1 h5 hS h hH hV hφ ht2 hAt hcard2 hE hOne hgen
  obtain ⟨p, hp, hpO⟩ := w16l_one_shape'
    (LinearEquiv.automorphismGroup.toLinearMapMonoidHom.comp ρ) ht2 hE hOne hgen hexp hTr
    (fun y _ => hTI y)
  refine ⟨⟨hcard0, Or.inr ⟨hn, ?_, p, hp, hpO⟩⟩, hcore⟩
  rw [hAt]
  exact hE

theorem w16l_threeFirst'_of_inputs {K : Type} [Group K] [Finite K] (hLie : SpPSULieFacts)
    (h711 : ∀ H : Subgroup K, W3Lem711Alt ↥H) : W3Lem85ThreeFirst' K := by
  have hRU := unitaryRootCommutatorRank_holds
  have hRL := l2RootCommutatorRank_of_irreducible l2IrreducibleRank_holds
  have g4 := w3Lem85TwoGap4_holds
  have g6 := w3Lem85TwoGap6_of_fact orth6MinusOddTranspFact_holds
  have hdisp : W3Lem85TwoDispatch K :=
    w3Lem85TwoDispatch_of_split h711 hRU hRL w3Lem85TwoGap1_holds w3Lem85TwoGap2_holds
      w3Lem85TwoGap3_holds g4 w3Lem85TwoGap5_holds g6
  have hKT : W3Lem85TwoKT K := w3Lem85TwoKT_of_bad (w3Lem85TwoBad_of_dispatch hdisp)
  exact w3Lem85ThreeFirst'_holds hLie hRU h711 g4 g6 hKT

theorem w16SixI_of_inputs (hLie : SpPSULieFacts) (hTim : TimmesfeldTIRootInput)
    (hGen : SevenK.TwoConjugateGeneration) (hCore : OddTranspositionCoreInputSC)
    (hList : OddTranspListBundle) (hIn : OrthReflParabolic)
    (h1 : W16One G) (h5 : W16Five G) : W16SixI G := by
  intro hS M V₀ V U S H h hH hV
  have hI : IsElemAbelian 2 (iSub16 V H) := Cex16.isElemAbelian_iSub16 h1 hS h hH.1
  have hJ : H ≤ Subgroup.normalizer (iSub16 V H : Set G) :=
    CFSG.Quasithin.le_normalizer_conjClosure _ _
  obtain ⟨D⟩ := exists_modDataE hI hJ
  have hIK := iSub16_le_conjClosure V H
  haveI hN : ((iSub16 V H).subgroupOf (CFSG.Quasithin.conjClosure V H)).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer hIK]
    exact fun k hk => hJ (IsMinFam16.conjClosure_le_H h hH hk)
  let φ := QuotientGroup.mk' ((iSub16 V H).subgroupOf (CFSG.Quasithin.conjClosure V H))
  have hφ : SevenK.IsBarMap (CFSG.Quasithin.conjClosure V H) (iSub16 V H) φ :=
    ⟨QuotientGroup.mk'_surjective _, fun k => by
      simp [φ, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]⟩
  have hF : W3Lem85ThreeFirst' (VG (D.img H)) :=
    w16l_threeFirst'_of_inputs hLie
      (A6Case.w3Lem711Alt_subgroups_of_inputs hTim hGen hCore hList hIn)
  have hShape := IsMinFam16.hatShape_img hTim hGen hCore hList hIn h1 h5 hS h hH hV D hF
  refine ⟨_, inferInstance, φ, hφ, ?_⟩
  rcases hShape.2 with ⟨hn, -⟩ | ⟨hn, -⟩
  · exact IsMinFam16.liftShape_many h1 h5 hS h hH hV D hφ hShape hn
  · exact IsMinFam16.liftShape_one h1 h5 hS h hH hV D hφ hShape hn

end Certified

end CFSG.LocalAnalysis.WeakClosure81

end
