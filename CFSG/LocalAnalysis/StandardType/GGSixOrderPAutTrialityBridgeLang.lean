module

public import CFSG.LocalAnalysis.StandardType.GGSixOrderPAutTrialityBridgeFix
public import CFSG.LocalAnalysis.StandardType.GGRecipeFieldExcLangTriD4
public import CFSG.RankThree.PartOne.KE.LangDescent

public section

namespace CFSG.StandardType

namespace TriBridge

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.StandardType.Triality
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

set_option linter.unusedSectionVars false

section Lang

variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem center_Om8_eq_bot : Subgroup.center (Om8 K) = ⊥ :=
  OrthRestOdd.center_matrixDerived_eq_bot
    (CFSG.ComponentClassification.CatalogueBOrthogonalPointData.regular_coordinateQuadPlus 4 K
      (by norm_num)).1 (by norm_num)

theorem mem_range_of_frobenius_fixed_D4 (L : Type) [Field L] [Algebra K L]
    [Algebra.IsAlgebraic K L] (Fr : L →+* L) (hFr : ∀ c, Fr c = c ^ Nat.card K)
    {h : ModGL TwistTag.D4.tag L} (hh : h ∈ adjointGroup TwistTag.D4.tag L)
    (hF : Units.map (entrywiseHom Fr) h = h) :
    ∃ g ∈ adjointGroup TwistTag.D4.tag K, baseChangeGL (algebraMap K L) g = h := by
  obtain ⟨a, u, ⟨j, hj, rfl⟩, hu⟩ :=
    exists_rootDiagUnit_mul_of_frobenius_fixed TwistTag.D4.tag Fr hFr hh hF
  have hT := (even_power_two_Cartan_root_diagonals_inner TwistTag.D4.tag
    (Or.inr (Or.inr (Or.inl rfl))) K (ringChar.eq K 2)).1 a
  have hle : torusGroup TwistTag.D4.tag K ≤ adjointGroup TwistTag.D4.tag K :=
    (Subgroup.closure_le _).2 fun _ ⟨q, hq⟩ => hq ▸ torusElt_mem_adjointGroup q.1 q.2
  exact ⟨rootDiagUnit TwistTag.D4.tag a * j, mul_mem (hle hT) hj, by rw [map_mul, hu]⟩

@[expose] noncomputable def bridgeEmb (L : Type) [Field L] [Algebra K L] :
    Om8 K →* adjointGroup TwistTag.D4.tag L :=
  ((baseChangeGL (algebraMap K L)).comp
    ((adjointGroup TwistTag.D4.tag K).subtype.comp (bridge (K := K)).toMonoidHom)).codRestrict _
    fun x => baseChangeGL_mem_adjointGroup (algebraMap K L) (bridge x).2

theorem coe_bridgeEmb (L : Type) [Field L] [Algebra K L] (x : Om8 K) :
    (bridgeEmb L x : ModGL TwistTag.D4.tag L) =
      baseChangeGL (algebraMap K L) (bridge x : ModGL TwistTag.D4.tag K) :=
  rfl

theorem bridgeEmb_injective (L : Type) [Field L] [Algebra K L] :
    Function.Injective (bridgeEmb (K := K) L) := fun _ _ h =>
  (bridge (K := K)).injective (Subtype.ext
    (baseChangeGL_injective (algebraMap K L) (congrArg Subtype.val h)))

theorem exists_conj_eq_of_lang_D4 {d : ℕ} (hd : 1 ≤ d) (hK : Nat.card K = (2 ^ d) ^ 3) (j : ℕ)
    (T : K ≃+* K) (hT : ∀ c, T c = c ^ (2 ^ d)) (F₁ : MulAut (Om8 K)) (hF₁3 : F₁ ^ 3 = 1)
    (hF₁ : ∀ x, (bridge (F₁ x) : ModGL TwistTag.D4.tag K) = diagramMap TwistTag.D4 K ^ j *
      Units.map (entrywiseHom T.toRingHom) (bridge x) * (diagramMap TwistTag.D4 K ^ j)⁻¹)
    (x : Om8 K) (hx : (MulAut.conj x * F₁) ^ 3 = 1) :
    ∃ g : Om8 K, MulAut.conj g * (MulAut.conj x * F₁) * (MulAut.conj g)⁻¹ = F₁ := by
  classical
  have : Fintype K := Fintype.ofFinite K
  set L := AlgebraicClosure K
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : CharP L 2 := charP_of_injective_algebraMap (algebraMap K L).injective 2
  obtain ⟨S, hLang, hSk⟩ := RecipeExcLang.exists_lang_twist TwistTag.D4 (L := L) hd j
  have hFrc : (iterateFrobenius L 2 d).comp (algebraMap K L) =
      (algebraMap K L).comp T.toRingHom := by
    ext c
    simp [iterateFrobenius_def, hT, map_pow]
  have heF : ∀ w, bridgeEmb L (F₁ w) = S (bridgeEmb L w) := by
    intro w
    apply Subtype.ext
    have h1 := hSk 1 (bridgeEmb L w)
    rw [pow_one, pow_one, mul_one] at h1
    rw [h1, coe_bridgeEmb, coe_bridgeEmb, hF₁, map_mul, map_mul, map_inv,
      map_pow, baseChangeGL_diagramMap, units_map_entrywiseHom_eq_baseChangeGL,
      units_map_entrywiseHom_eq_baseChangeGL, baseChangeGL_baseChangeGL,
      baseChangeGL_baseChangeGL, hFrc]
  have hP3 : diagramMap TwistTag.D4 L ^ (j * 3) = 1 := by
    rw [pow_mul', show diagramMap TwistTag.D4 L ^ 3 = 1 from diagramMap_pow_order TwistTag.D4 L,
      one_pow]
  have hFrK : ∀ c : L, ((iterateFrobenius L 2 d) ^ 3) c = c ^ Nat.card K := by
    intro c
    rw [RingHom.coe_pow]
    simp only [Function.iterate_succ, Function.iterate_zero, Function.comp_apply, id_eq,
      iterateFrobenius_def]
    rw [← pow_mul, ← pow_mul, hK]
    ring
  have hmem : ∀ h : adjointGroup TwistTag.D4.tag L, (S ^ 3) h = h → h ∈ (bridgeEmb (K := K) L).range := by
    intro h hh
    have hfix : Units.map (entrywiseHom ((iterateFrobenius L 2 d) ^ 3))
        (h : ModGL TwistTag.D4.tag L) = h := by
      have h1 := hSk 3 h
      rw [hh, hP3, one_mul, inv_one, mul_one] at h1
      exact h1.symm
    obtain ⟨g, hg, hgh⟩ := mem_range_of_frobenius_fixed_D4 (K := K) L _ hFrK h.2 hfix
    refine ⟨bridge.symm ⟨g, hg⟩, Subtype.ext ?_⟩
    rw [coe_bridgeEmb, MulEquiv.apply_symm_apply]
    exact hgh
  exact CFSG.RankThree.PartOne.KE.exists_inner_conj_eq_of_lang center_Om8_eq_bot F₁
    (by norm_num) hF₁3 S hLang (bridgeEmb L) (bridgeEmb_injective L) heF hmem x hx

theorem theta_fieldAutP_cube (σ : K ≃+* K) (hσ : σ ^ 3 = 1) :
    (theta * AutOm.fieldAutP 4 σ : MulAut (Om8 K)) ^ 3 = 1 := by
  have hc : Commute (theta : MulAut (Om8 K)) (AutOm.fieldAutP 4 σ) := theta_fieldAutP σ
  rw [hc.mul_pow, theta_cube, ← map_pow, hσ, map_one, one_mul]

theorem coe_bridge_inv_theta_fieldAutP (σ : K ≃+* K) (x : Om8 K) :
    (bridge ((theta * AutOm.fieldAutP 4 σ : MulAut (Om8 K))⁻¹ x) : ModGL TwistTag.D4.tag K) =
      diagramMap TwistTag.D4 K ^ 2 * Units.map (entrywiseHom σ⁻¹.toRingHom) (bridge x) *
        (diagramMap TwistTag.D4 K ^ 2)⁻¹ := by
  set F₀ := (theta * AutOm.fieldAutP 4 σ : MulAut (Om8 K))
  set y := F₀⁻¹ x
  have hy : F₀ y = x := by
    change F₀ (F₀.symm x) = x
    exact F₀.apply_symm_apply x
  have hbx : (bridge x : ModGL TwistTag.D4.tag K) = diagramMap TwistTag.D4 K *
      Units.map (entrywiseHom σ.toRingHom) (bridge y) * (diagramMap TwistTag.D4 K)⁻¹ := by
    rw [← hy, ← twistHom_apply]
    exact coe_bridge_theta_fieldAutP σ y
  have hid : σ⁻¹.toRingHom.comp σ.toRingHom = RingHom.id K := by
    ext c
    change σ.symm (σ c) = c
    exact σ.symm_apply_apply c
  have hP3 : diagramMap TwistTag.D4 K ^ 3 = 1 := diagramMap_pow_order TwistTag.D4 K
  rw [hbx, map_mul, map_mul, map_inv, units_map_entrywiseHom_diagramMap,
    units_map_entrywiseHom_comp, hid, RecipeExcLang.units_map_entrywiseHom_id]
  calc (bridge y : ModGL TwistTag.D4.tag K)
      = diagramMap TwistTag.D4 K ^ 3 * (bridge y : ModGL TwistTag.D4.tag K) *
          (diagramMap TwistTag.D4 K ^ 3)⁻¹ := by rw [hP3, one_mul, inv_one, mul_one]
    _ = _ := by group

end Lang

section Input


theorem ggD4GraphFieldLangInput_holds : GGD4GraphFieldLangInput := by
  intro K _ _ _ σ hσ γ hβ
  obtain ⟨d, hd, hK, r, hr, hσr⟩ := exists_frob_of_orderOf_three σ hσ
  have hσ3 : σ ^ 3 = 1 := by rw [← hσ]; exact pow_orderOf_eq_one σ
  set F₀ := (theta * AutOm.fieldAutP 4 σ : MulAut (Om8 K)) with hF₀
  have hF₀3 : F₀ ^ 3 = 1 := theta_fieldAutP_cube σ hσ3
  rcases hr with rfl | rfl
  ·
    have hF₁ : ∀ x, (bridge (F₀ x) : ModGL TwistTag.D4.tag K) = diagramMap TwistTag.D4 K ^ 1 *
        Units.map (entrywiseHom σ.toRingHom) (bridge x) * (diagramMap TwistTag.D4 K ^ 1)⁻¹ := by
      intro x
      rw [pow_one, ← twistHom_apply]
      exact coe_bridge_theta_fieldAutP σ x
    obtain ⟨g, hg⟩ := exists_conj_eq_of_lang_D4 hd hK 1 σ (fun c => by rw [hσr, pow_one]) F₀
      hF₀3 hF₁ γ hβ
    have hB : MulAut.conj γ * F₀ = (MulAut.conj g)⁻¹ * F₀ * MulAut.conj g :=
      calc MulAut.conj γ * F₀ = (MulAut.conj g)⁻¹ *
            (MulAut.conj g * (MulAut.conj γ * F₀) * (MulAut.conj g)⁻¹) * MulAut.conj g := by
            group
        _ = _ := by rw [hg]
    exact ⟨g⁻¹, by rw [hB, map_inv, inv_inv]⟩
  ·
    have hT : ∀ c, (σ⁻¹ : K ≃+* K) c = c ^ (2 ^ d) := by
      intro c
      have : Fintype K := Fintype.ofFinite K
      have h1 : (σ⁻¹ : K ≃+* K) = σ ^ 2 := by
        rw [inv_eq_iff_mul_eq_one, ← pow_succ']
        exact hσ3
      rw [h1, pow_two, RingAut.mul_apply, hσr, hσr, ← pow_mul,
        show (2 ^ d) ^ 2 * (2 ^ d) ^ 2 = (2 ^ d) ^ 3 * 2 ^ d by ring, pow_mul, ← hK,
        Nat.card_eq_fintype_card, FiniteField.pow_card]
    have hF₁3 : F₀⁻¹ ^ 3 = 1 := by rw [inv_pow, hF₀3, inv_one]
    have key : (MulAut.conj γ * F₀)⁻¹ = MulAut.conj (F₀⁻¹ γ⁻¹) * F₀⁻¹ := by
      rw [← OrthRestOdd.conj_map_mulAut F₀⁻¹ γ⁻¹, map_inv]
      group
    have hx : (MulAut.conj (F₀⁻¹ γ⁻¹) * F₀⁻¹) ^ 3 = 1 := by
      rw [← key, inv_pow, hβ, inv_one]
    obtain ⟨g, hg⟩ := exists_conj_eq_of_lang_D4 hd hK 2 σ⁻¹ hT F₀⁻¹ hF₁3
      (coe_bridge_inv_theta_fieldAutP σ) _ hx
    rw [← key] at hg
    have h1 : (MulAut.conj γ * F₀)⁻¹ = (MulAut.conj g)⁻¹ * F₀⁻¹ * MulAut.conj g :=
      calc (MulAut.conj γ * F₀)⁻¹ = (MulAut.conj g)⁻¹ *
            (MulAut.conj g * (MulAut.conj γ * F₀)⁻¹ * (MulAut.conj g)⁻¹) * MulAut.conj g := by
            group
        _ = _ := by rw [hg]
    have hB : MulAut.conj γ * F₀ = (MulAut.conj g)⁻¹ * F₀ * MulAut.conj g :=
      calc MulAut.conj γ * F₀ = ((MulAut.conj γ * F₀)⁻¹)⁻¹ := (inv_inv _).symm
        _ = ((MulAut.conj g)⁻¹ * F₀⁻¹ * MulAut.conj g)⁻¹ := by rw [h1]
        _ = _ := by group
    exact ⟨g⁻¹, by rw [hB, map_inv, inv_inv]⟩

end Input

end TriBridge

end CFSG.StandardType
