module

public import CFSG.LocalAnalysis.StandardType.GGD4OddCentGraphMark
public import CFSG.LocalAnalysis.StandardType.GGD4OddCentGraphPGU
public import CFSG.LocalAnalysis.StandardType.GGFieldCaseL45RankXTriality
public import CFSG.LocalAnalysis.StandardType.GGD4OddCentFieldReduce
public import CFSG.LocalAnalysis.StandardType.GGSixOrderPAutTrialityBridgeFix
public import CFSG.LocalAnalysis.StandardType.GGSixOrderPAutTrialityBridgeLang
public import CFSG.LocalAnalysis.StandardType.GGSixOrderPAutTrialityLayer
import CFSG.LocalAnalysis.StandardType.GGSixOrderPAutTrialityBridgeClassInput
import CFSG.LocalAnalysis.StandardType.GGD4OddCentFieldFixed
import CFSG.LocalAnalysis.StandardType.GGTableBExcSmallRestTri

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.AlgebraicGroups CFSG.StandardType.Triality CFSG.RankThree.PartTwo.Sec8
  CFSG.ComponentClassification.OuterAutomorphisms

open TriBridge

theorem ggD4OddCent_graphClass
    {K : Type} [Field K] [Finite K] [CharP K 2] (γ : Om8 K)
    (hβ : (MulAut.conj γ * theta) ^ 3 = 1) :
    (∃ g : Om8 K, MulAut.conj γ * theta = MulAut.conj g * theta * (MulAut.conj g)⁻¹) ∨
      Nonempty (↥(ggFix (MulAut.conj γ * theta)) ≃*
        ↥(graphCentralizer TwistTag.D4.tag K (d4TrialityY0 K * (diagramMap TwistTag.D4 K)⁻¹))) := by
  obtain ⟨b, hb⟩ : ∃ b, (bridge γ : ModGL TwistTag.D4.tag K) = b := ⟨_, rfl⟩
  have hbG : b ∈ adjointGroup TwistTag.D4.tag K := hb ▸ (bridge γ).2
  have hN : (b * diagramMap TwistTag.D4 K) ^ 3 = 1 := by
    rw [← hb]
    exact bridge_mul_diagramMap_pow_three hβ
  have hxG : (diagramMap TwistTag.D4 K)⁻¹ * b⁻¹ * diagramMap TwistTag.D4 K ∈
      adjointGroup TwistTag.D4.tag K := diagramMap_inv_conj_mem (inv_mem hbG)
  have hxs : (diagramMap TwistTag.D4 K)⁻¹ * b⁻¹ * diagramMap TwistTag.D4 K *
      (diagramMap TwistTag.D4 K)⁻¹ = (b * diagramMap TwistTag.D4 K)⁻¹ := by group
  have hx3 : ((diagramMap TwistTag.D4 K)⁻¹ * b⁻¹ * diagramMap TwistTag.D4 K *
      (diagramMap TwistTag.D4 K)⁻¹) ^ 3 = 1 := by
    rw [hxs, inv_pow, hN, inv_one]
  obtain ⟨y, hy, hcase⟩ := exists_conj_classes_D4 hxG hx3
  rw [hxs] at hcase
  rcases hcase with h1 | h2
  · left
    have hg : (bridge ((bridge (K := K)).symm ⟨y, hy⟩) : ModGL TwistTag.D4.tag K) = y := by
      rw [MulEquiv.apply_symm_apply]
    have hP' : y * (b * diagramMap TwistTag.D4 K) * y⁻¹ = diagramMap TwistTag.D4 K :=
      calc y * (b * diagramMap TwistTag.D4 K) * y⁻¹ =
            (y * (b * diagramMap TwistTag.D4 K)⁻¹ * y⁻¹)⁻¹ := by group
        _ = ((diagramMap TwistTag.D4 K)⁻¹)⁻¹ := by rw [h1]
        _ = diagramMap TwistTag.D4 K := inv_inv _
    set g := (bridge (K := K)).symm ⟨y, hy⟩ with hgdef
    have hconj : MulAut.conj g * (MulAut.conj γ * theta) * (MulAut.conj g)⁻¹ = theta := by
      refine MulEquiv.ext fun z => ?_
      apply (bridge (K := K)).injective
      apply Subtype.ext
      rw [MulAut.mul_apply, MulAut.mul_apply, MulAut.conj_inv_apply, MulAut.conj_apply,
        map_mul, map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv,
        coe_bridge_conj_theta, map_mul, map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_mul,
        Subgroup.coe_inv, hg, hb, coe_bridge_theta]
      calc y * (b * diagramMap TwistTag.D4 K * (y⁻¹ * (bridge z : ModGL TwistTag.D4.tag K) * y) *
            (b * diagramMap TwistTag.D4 K)⁻¹) * y⁻¹ =
            (y * (b * diagramMap TwistTag.D4 K) * y⁻¹) * (bridge z : ModGL TwistTag.D4.tag K) *
              (y * (b * diagramMap TwistTag.D4 K) * y⁻¹)⁻¹ := by group
        _ = _ := by rw [hP']
    refine ⟨g⁻¹, ?_⟩
    rw [map_inv, inv_inv]
    calc MulAut.conj γ * theta = (MulAut.conj g)⁻¹ *
          (MulAut.conj g * (MulAut.conj γ * theta) * (MulAut.conj g)⁻¹) * MulAut.conj g := by
          group
      _ = _ := by rw [hconj]
  · right
    have hmap := map_ggFix_eq_graphCentralizer (γ := γ) hy
    rw [hb, h2] at hmap
    have hinj : Function.Injective ((MulAut.conj y).toMonoidHom.comp
        ((adjointGroup TwistTag.D4.tag K).subtype.comp (bridge (K := K)).toMonoidHom)) :=
      (MulAut.conj y).injective.comp (Subtype.val_injective.comp (bridge (K := K)).injective)
    exact ⟨((ggFix (MulAut.conj γ * theta)).equivMapOfInjective _ hinj).trans
      (MulEquiv.subgroupCongr hmap)⟩

private theorem theta_mul_fieldAutP_eq_plusRefl_conj {K : Type} [Field K] [Finite K] [CharP K 2]
    (τ : K ≃+* K) :
    (theta : MulAut (Om8 K)) * AutOm.fieldAutP 4 τ =
      AutOm.plusRefl (K := K) one_le_four * (theta * AutOm.fieldAutP 4 τ⁻¹)⁻¹ *
        (AutOm.plusRefl (K := K) one_le_four)⁻¹ := by
  let ρ : MulAut (Om8 K) := AutOm.plusRefl one_le_four
  have hρ2 : ρ * ρ = 1 := AutOm.plusRefl_mul_self one_le_four
  have hρinv : ρ⁻¹ = ρ := inv_eq_of_mul_eq_one_right hρ2
  have hρφ : ρ * AutOm.fieldAutP 4 τ = AutOm.fieldAutP 4 τ * ρ :=
    AutOm.plusRefl_mul_fieldAutP one_le_four τ
  have hρθ : ρ * (theta : MulAut (Om8 K)) * ρ = theta⁻¹ := plusRefl_theta_plusRefl
  have hρθinv : ρ * (theta : MulAut (Om8 K))⁻¹ * ρ = theta := by
    calc ρ * (theta : MulAut (Om8 K))⁻¹ * ρ = (ρ * theta * ρ)⁻¹ := by
          rw [mul_inv_rev, mul_inv_rev, hρinv]; group
      _ = (theta⁻¹)⁻¹ := by rw [hρθ]
      _ = theta := inv_inv _
  have hA : (theta * AutOm.fieldAutP 4 τ⁻¹)⁻¹ = AutOm.fieldAutP 4 τ * theta⁻¹ := by
    refine inv_eq_of_mul_eq_one_right ?_
    calc theta * AutOm.fieldAutP 4 τ⁻¹ * (AutOm.fieldAutP 4 τ * theta⁻¹)
        = theta * (AutOm.fieldAutP 4 τ⁻¹ * AutOm.fieldAutP 4 τ) * theta⁻¹ := by group
      _ = theta * AutOm.fieldAutP 4 (τ⁻¹ * τ) * theta⁻¹ := by rw [← map_mul]
      _ = theta * AutOm.fieldAutP 4 1 * theta⁻¹ := by rw [inv_mul_cancel]
      _ = theta * 1 * theta⁻¹ := by rw [map_one]
      _ = 1 := by group
  have hR : ρ * (theta * AutOm.fieldAutP 4 τ⁻¹)⁻¹ * ρ⁻¹ =
      (theta : MulAut (Om8 K)) * AutOm.fieldAutP 4 τ := by
    rw [hA, hρinv]
    calc ρ * (AutOm.fieldAutP 4 τ * theta⁻¹) * ρ
        = ρ * AutOm.fieldAutP 4 τ * theta⁻¹ * ρ := by group
      _ = AutOm.fieldAutP 4 τ * ρ * theta⁻¹ * ρ := by rw [hρφ]
      _ = AutOm.fieldAutP 4 τ * (ρ * theta⁻¹ * ρ) := by group
      _ = AutOm.fieldAutP 4 τ * theta := by rw [hρθinv]
      _ = theta * AutOm.fieldAutP 4 τ := (theta_fieldAutP τ).symm
  exact hR.symm

private theorem ggD4OddCent_fieldFixedData
    {K : Type} [Field K] [Finite K] [CharP K 2]
    {d : ℕ} (hd : 1 ≤ d) (hKd : Nat.card K = (2 ^ d) ^ 3) {τ₁ : K ≃+* K}
    (hτ₁ : ∀ c, τ₁ c = c ^ 2 ^ d) :
    twistedFixedGroup TwistTag.D4 K τ₁.toRingHom = graphFixedRootGroup TwistTag.D4 K τ₁.toRingHom ∧
      IsSimpleGroup (graphFixedRootGroup TwistTag.D4 K τ₁.toRingHom) ∧
      ∃ x y : graphFixedRootGroup TwistTag.D4 K τ₁.toRingHom, x * y ≠ y * x := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : CharP (AlgebraicClosure K) 2 :=
    charP_of_injective_algebraMap (algebraMap K (AlgebraicClosure K)).injective 2
  obtain ⟨-, -, hfix, hsimple, x, y, hxy⟩ :=
    triality_both_field_orientations_simple_full_ambient_fixed_group 2 d Nat.prime_two hd K hKd
      (AlgebraicClosure K) 1 (Or.inl rfl) τ₁.toRingHom (fun c => by simpa using hτ₁ c)
      (iterateFrobenius (AlgebraicClosure K) 2 d)
      (fun c => iterateFrobenius_def 2 d c)
  exact ⟨hfix, hsimple, x, y, hxy⟩

private theorem ggD4OddCent_outerShape_core
    {K : Type} [Field K] [Finite K] [CharP K 2] {n : ℕ}
    (hK : Nat.card K = 2 ^ n) (hn : Odd n) {τ : K ≃+* K} (hτ3 : τ ^ 3 = 1)
    {γ' : Om8 K} (h3 : (MulAut.conj γ' * (theta * AutOm.fieldAutP 4 τ)) ^ 3 = 1) :
    GGD4OddCentOuterShape n
      ↥(ggFix (MulAut.conj γ' * (theta * AutOm.fieldAutP 4 τ))) := by
  by_cases hτ1 : τ = 1
  · rw [hτ1, map_one, mul_one] at h3 ⊢
    rcases ggD4OddCent_graphClass γ' h3 with hconj | he
    · left
      obtain ⟨g, hg⟩ := hconj
      have hmap : ggFix (MulAut.conj γ' * (theta : MulAut (Om8 K))) =
          (ggFix (theta : MulAut (Om8 K))).map (MulAut.conj g).toMonoidHom := by
        rw [hg, OrdPTriLayer.ggFix_mul_mul_inv]
      have h2 : (2 : K) = 0 := CharP.cast_eq_zero K 2
      have hθ : (theta : MulAut (Om8 K)) = theta * AutOm.fieldAutP 4 1 := by
        rw [map_one, mul_one]
      have e1 : ↥(ggFix (theta : MulAut (Om8 K))) ≃* ↥(adjointGroup Tag.G2 K) :=
        ((MulEquiv.subgroupCongr (congrArg ggFix hθ)).trans (ggFixEquiv (K := K) 1)).trans
          (CFSG.RankThree.PartTwo.KFacts.d4FixedG2Equiv K h2)
      have e2 : ↥(ggFix (MulAut.conj γ' * (theta : MulAut (Om8 K)))) ≃*
          ↥(ggFix (theta : MulAut (Om8 K))) :=
        (MulEquiv.subgroupCongr hmap).trans
          (Subgroup.equivMapOfInjective (ggFix (theta : MulAut (Om8 K)))
            (MulAut.conj g).toMonoidHom (MulAut.conj g).injective).symm
      exact ⟨K, inferInstance, inferInstance, hK, ⟨e2.trans e1⟩⟩
    · right
      obtain ⟨e⟩ := he
      obtain ⟨F, hFf, hFi, hFcard, ⟨e2⟩⟩ := ggD4OddCent_secondCent_isoPGU hn hK
      exact Or.inl ⟨F, hFf, hFi, hFcard, ⟨e.trans e2⟩⟩
  · haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    have hτo : orderOf τ = 3 := orderOf_eq_prime hτ3 hτ1
    obtain ⟨d, hd, hKd, r, hr, hτr⟩ := exists_frob_of_orderOf_three τ hτo
    have hn3 : n = 3 * d := by
      have h1 : 2 ^ n = 2 ^ (d * 3) := by rw [← hK, hKd, pow_mul]
      have h2 := Nat.pow_right_injective (a := 2) (by norm_num) h1
      omega
    obtain ⟨g, hg⟩ := ggD4GraphFieldLangInput_holds K τ hτo γ' h3
    have hmap1 : ggFix (MulAut.conj γ' * (theta * AutOm.fieldAutP 4 τ)) =
        (ggFix (theta * AutOm.fieldAutP 4 τ)).map (MulAut.conj g).toMonoidHom := by
      rw [hg, OrdPTriLayer.ggFix_mul_mul_inv]
    have e_conj : ↥(ggFix (MulAut.conj γ' * (theta * AutOm.fieldAutP 4 τ))) ≃*
        ↥(ggFix (theta * AutOm.fieldAutP 4 τ)) :=
      (MulEquiv.subgroupCongr hmap1).trans
        (Subgroup.equivMapOfInjective (ggFix (theta * AutOm.fieldAutP 4 τ))
          (MulAut.conj g).toMonoidHom (MulAut.conj g).injective).symm
    rcases hr with rfl | rfl
    · have hτ1d : ∀ c, τ c = c ^ 2 ^ d := fun c => by simpa using hτr c
      obtain ⟨hfix, hsimple, hnc⟩ := ggD4OddCent_fieldFixedData hd hKd hτ1d
      have e_θ : ↥(ggFix (theta * AutOm.fieldAutP 4 τ)) ≃*
          graphFixedRootGroup TwistTag.D4 K τ.toRingHom :=
        (ggFixEquiv τ).trans (MulEquiv.subgroupCongr hfix)
      obtain ⟨e_tri⟩ := TableBExcSmallRest.nonempty_triD4_equiv hd K hKd τ hτ1d
      have e_total := e_conj.trans e_θ
      haveI := hsimple
      have e_final : ↥(ggFix (MulAut.conj γ' * (theta * AutOm.fieldAutP 4 τ))) ≃*
          GGTriD4R d K := e_total.trans e_tri.symm
      refine Or.inr (Or.inr ⟨d, K, inferInstance, inferInstance, hd, hn3, hKd, ?_, ?_,
        ⟨e_final⟩⟩)
      · exact e_total.isSimpleGroup
      · obtain ⟨x, y, hxy⟩ := hnc
        refine ⟨e_total.symm x, e_total.symm y, fun h => hxy ?_⟩
        have h' := congrArg e_total h
        simpa only [map_mul, MulEquiv.apply_symm_apply] using h'
    · have hτi : ∀ c, (τ⁻¹ : K ≃+* K) c = c ^ 2 ^ d := by
        intro c
        have hpow : (2 ^ d) ^ 2 * 2 ^ d = (2 ^ d) ^ 3 := by rw [← pow_succ]
        haveI : Fintype K := Fintype.ofFinite K
        have h : τ (c ^ 2 ^ d) = c := by
          rw [map_pow, hτr, ← pow_mul, hpow, ← hKd, Nat.card_eq_fintype_card,
            FiniteField.pow_card]
        calc (τ⁻¹ : K ≃+* K) c = τ⁻¹ (τ (c ^ 2 ^ d)) := by rw [h]
          _ = c ^ 2 ^ d := τ.symm_apply_apply _
      obtain ⟨hfix, hsimple, hnc⟩ := ggD4OddCent_fieldFixedData hd hKd hτi
      have hmain := theta_mul_fieldAutP_eq_plusRefl_conj τ
      have hmapρ : ggFix (theta * AutOm.fieldAutP 4 τ) =
          (ggFix (theta * AutOm.fieldAutP 4 τ⁻¹)).map
            (AutOm.plusRefl (K := K) one_le_four).toMonoidHom := by
        rw [hmain, OrdPTriLayer.ggFix_mul_mul_inv, OrdPTriLayer.ggFix_inv]
      have e_ρ : ↥(ggFix (theta * AutOm.fieldAutP 4 τ)) ≃*
          ↥(ggFix (theta * AutOm.fieldAutP 4 τ⁻¹)) :=
        (MulEquiv.subgroupCongr hmapρ).trans
          (Subgroup.equivMapOfInjective (ggFix (theta * AutOm.fieldAutP 4 τ⁻¹))
            (AutOm.plusRefl (K := K) one_le_four).toMonoidHom
            (AutOm.plusRefl (K := K) one_le_four).injective).symm
      have e_θ : ↥(ggFix (theta * AutOm.fieldAutP 4 τ)) ≃*
          graphFixedRootGroup TwistTag.D4 K (τ⁻¹).toRingHom :=
        e_ρ.trans ((ggFixEquiv τ⁻¹).trans (MulEquiv.subgroupCongr hfix))
      obtain ⟨e_tri⟩ := TableBExcSmallRest.nonempty_triD4_equiv hd K hKd τ⁻¹ hτi
      have e_total := e_conj.trans e_θ
      haveI := hsimple
      have e_final : ↥(ggFix (MulAut.conj γ' * (theta * AutOm.fieldAutP 4 τ))) ≃*
          GGTriD4R d K := e_total.trans e_tri.symm
      refine Or.inr (Or.inr ⟨d, K, inferInstance, inferInstance, hd, hn3, hKd, ?_, ?_,
        ⟨e_final⟩⟩)
      · exact e_total.isSimpleGroup
      · obtain ⟨x, y, hxy⟩ := hnc
        refine ⟨e_total.symm x, e_total.symm y, fun h => hxy ?_⟩
        have h' := congrArg e_total h
        simpa only [map_mul, MulEquiv.apply_symm_apply] using h'

theorem ggD4OddCent_outerShape_om8
    {K : Type} [Field K] [Finite K] [CharP K 2] {n : ℕ}
    (hK : Nat.card K = 2 ^ n) (hn : Odd n) {β : MulAut (Om8 K)} (hβ3 : β ^ 3 = 1)
    (hβ : β ∉ inner (Om8 K) ⊔ (AutOm.fieldAutP 4).range) :
    GGD4OddCentOuterShape n ↥(ggFix β) := by
  obtain ⟨γ, k, σ, hk, rfl⟩ :=
    L45RankX.exists_conj_theta_pow_fieldAutP_of_pow (e := 1) (by simpa using hβ3) hβ
  have hσ3 : σ ^ 3 = 1 := OrdPTriLayer.cube_eq_one_of_conj_mul_cube hβ3
  rcases hk with rfl | rfl
  · rw [pow_one] at hβ3 ⊢
    exact ggD4OddCent_outerShape_core hK hn hσ3 hβ3
  · have hinv := OrdPTriLayer.conj_mul_inv_eq γ (OrdPTriLayer.theta_sq_mul_fieldAutP_inv σ)
    have h3 : (MulAut.conj ((theta * AutOm.fieldAutP 4 σ⁻¹ : MulAut (Om8 K)) γ⁻¹) *
        (theta * AutOm.fieldAutP 4 σ⁻¹)) ^ 3 = 1 := by
      rw [← hinv, inv_pow, hβ3, inv_one]
    have hσi3 : (σ⁻¹ : K ≃+* K) ^ 3 = 1 := by rw [inv_pow, hσ3, inv_one]
    have hcore := ggD4OddCent_outerShape_core hK hn hσi3 h3
    rw [← hinv, OrdPTriLayer.ggFix_inv] at hcore
    exact hcore

theorem ggD4OddCent_outerShape
    {K : Type} [Field K] [Finite K] {n : ℕ}
    (hK : Nat.card K = 2 ^ n) (hn : Odd n) {s : MulAut (D4Recipe K)} (hs3 : s ^ 3 = 1)
    (hs : ¬ GGInnField (LargeEvenInnSet (D4Recipe K)) (D4FieldSet K) s) :
    GGD4OddCentOuterShape n ↥(ggAutFixedSubgroup s) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fintype K := Fintype.ofFinite K
  haveI : CharP K 2 :=
    charP_of_card_eq_prime_pow (p := 2) (f := n) (by rw [← Nat.card_eq_fintype_card, hK])
  set Θ : D4Recipe K ≃* Om8 K := RecipeFieldOmega.plusEquiv (K := K) (m := 4) one_le_four
  let β : MulAut (Om8 K) := MulAut.congr Θ s
  have hβ3 : β ^ 3 = 1 := by
    change (MulAut.congr Θ s) ^ 3 = 1
    rw [← map_pow, hs3, map_one]
  have hβ : β ∉ inner (Om8 K) ⊔ (AutOm.fieldAutP 4).range := by
    intro hmem
    obtain ⟨u, hu, f, hf, huf⟩ := Subgroup.mem_sup_of_normal_left.1 hmem
    have hu' : (MulAut.congr Θ).symm u ∈ LargeEvenInnSet (D4Recipe K) :=
      (RecipeFieldOmega.mem_innSet_iff_congr Θ _).2 (by rw [MulEquiv.apply_symm_apply]; exact hu)
    obtain ⟨σ, hσ⟩ := hf
    obtain ⟨φ', hφ', hφ'eq⟩ :=
      RecipeFieldOmega.exists_mem_field_congr_plusEquiv (K := K) (m := 4) one_le_four σ
    have hf' : (MulAut.congr Θ).symm f ∈ D4FieldSet K := by
      rw [← hσ, ← hφ'eq, MulEquiv.symm_apply_apply]
      exact hφ'
    have hs_eq : s = (MulAut.congr Θ).symm u * (MulAut.congr Θ).symm f := by
      apply (MulAut.congr Θ).injective
      rw [map_mul, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply]
      exact huf.symm
    exact hs ⟨_, hu', _, Subgroup.subset_closure hf', hs_eq⟩
  have hshape := ggD4OddCent_outerShape_om8 hK hn hβ3 hβ
  have hfixeq : ggAutFixedSubgroup β = (ggAutFixedSubgroup s).map Θ.toMonoidHom :=
    gdf_fixed_congr Θ s
  have hcarrier : ggAutFixedSubgroup β = ggFix β := Subgroup.ext fun _ => Iff.rfl
  have e1 : ↥(ggAutFixedSubgroup s) ≃*
      ↥((ggAutFixedSubgroup s).map Θ.toMonoidHom) :=
    Subgroup.equivMapOfInjective (ggAutFixedSubgroup s) Θ.toMonoidHom Θ.injective
  have e2 : ↥((ggAutFixedSubgroup s).map Θ.toMonoidHom) ≃* ↥(ggAutFixedSubgroup β) :=
    MulEquiv.subgroupCongr hfixeq.symm
  have e3 : ↥(ggAutFixedSubgroup β) ≃* ↥(ggFix β) := MulEquiv.subgroupCongr hcarrier
  exact GGD4OddCentOuterShape.of_mulEquiv (e1.trans (e2.trans e3)) hshape

end CFSG.StandardType
