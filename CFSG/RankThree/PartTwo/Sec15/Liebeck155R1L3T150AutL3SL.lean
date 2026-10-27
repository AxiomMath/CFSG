module

public import CFSG.RankThree.PartTwo.Sec4.RonanK429RowLieField
public import CFSG.RankThree.PartTwo.Sec15.Liebeck155R1L3T150Defs
public import CFSG.Timmesfeld.Orders.Distinct
public import CFSG.CharacterTheory.Wreathed.CentralSL2Abelianization
public import CFSG.RankThree.PartTwo.Sec4.Item47Inputs

public section

namespace CFSG.RankThree.PartTwo.Sec15.Liebeck155R1L3T150

open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag Matrix
open CFSG.GH74.GLS.IVK (fixedField)
open CFSG.RankThree.PartTwo.Sec4.RonanK429Lie (linFix linFixEquiv comapEquiv eq_comap_range_linFix
  commutator_mem_range_linFix)
open CFSG.Timmesfeld CFSG.Timmesfeld.Orders
open scoped commutatorElement
open CFSG.RankThree.PartTwo.KFacts

section Linear

variable {F : Type} [Field F]

private noncomputable def elemSL (i j : Fin 3) (hij : i ≠ j) (a : F) :
    Matrix.SpecialLinearGroup (Fin 3) F :=
  ⟨transvection i j a, det_transvection_of_ne i j hij a⟩

private theorem coe_elemSL (i j : Fin 3) (hij : i ≠ j) (a : F) :
    (elemSL i j hij a : Matrix (Fin 3) (Fin 3) F) = 1 + single i j a := rfl

private theorem exists_smul_of_proj_eq {X g : Matrix.SpecialLinearGroup (Fin 3) F}
    (h : proj 3 F X = proj 3 F g) :
    ∃ c : F, c ^ 3 = 1 ∧
      (g : Matrix (Fin 3) (Fin 3) F) = c • (X : Matrix (Fin 3) (Fin 3) F) := by
  rw [proj_eq_proj_iff, mem_scalars] at h
  obtain ⟨c, hc, hcm⟩ := h
  refine ⟨c, ?_, ?_⟩
  · have := congrArg Units.val hc
    simpa using this
  · have hg : (g : Matrix (Fin 3) (Fin 3) F) =
        (X : Matrix (Fin 3) (Fin 3) F) * ((X⁻¹ * g : Matrix.SpecialLinearGroup (Fin 3) F) :
          Matrix (Fin 3) (Fin 3) F) := by
      rw [← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel_left]
    rw [hg, hcm, Matrix.scalar_apply]
    ext i j
    simp [Matrix.mul_apply, Matrix.diagonal_apply, mul_comm]

private theorem eq_one_of_cube_of_three_mul {c : F} (hc : c ^ 3 = 1) (h : 3 * c = 3) :
    c = 1 := by
  by_cases h3 : (3 : F) = 0
  · have : (c - 1) ^ 3 = 0 := by linear_combination hc + (c - c ^ 2) * h3
    exact sub_eq_zero.mp (pow_eq_zero_iff (by norm_num) |>.mp this)
  · exact mul_left_cancel₀ h3 (by rw [h]; ring)

private theorem std0_apply (A : GL (Fin 3) F) (δ : F ≃+* F)
    (g : Matrix.SpecialLinearGroup (Fin 3) F) :
    (conjAut 3 F A * fieldAut 3 F δ) (proj 3 F g) =
      proj 3 F (CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation 3 F A
        (Matrix.SpecialLinearGroup.map δ.toRingHom g)) := by
  rw [MulAut.mul_apply, fieldAut_proj, conjAut_proj]

private theorem fix0 {A : GL (Fin 3) F} {δ : F ≃+* F}
    {g : Matrix.SpecialLinearGroup (Fin 3) F}
    (h : (conjAut 3 F A * fieldAut 3 F δ) (proj 3 F g) = proj 3 F g) :
    ∃ c : F, c ^ 3 = 1 ∧ (g : Matrix (Fin 3) (Fin 3) F) =
      c • ((A : Matrix (Fin 3) (Fin 3) F) * (g : Matrix (Fin 3) (Fin 3) F).map δ *
        ((A⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)) := by
  rw [std0_apply] at h
  obtain ⟨c, hc, hcm⟩ := exists_smul_of_proj_eq h
  refine ⟨c, hc, ?_⟩
  have e1 : ((CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation 3 F A
      (Matrix.SpecialLinearGroup.map δ.toRingHom g) : Matrix.SpecialLinearGroup (Fin 3) F) :
        Matrix (Fin 3) (Fin 3) F) =
      (A : Matrix (Fin 3) (Fin 3) F) * (g : Matrix (Fin 3) (Fin 3) F).map δ *
        ((A⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) := by
    rw [CFSG.LocalAnalysis.ComponentInitial.LinearFlag.coe_slConjugation,
      Matrix.SpecialLinearGroup.map_apply_coe]
    rfl
  rw [e1] at hcm
  exact hcm

private theorem map_coe_elemSL (δ : F ≃+* F) (i j : Fin 3) (hij : i ≠ j) (a : F) :
    (elemSL i j hij a : Matrix (Fin 3) (Fin 3) F).map δ = 1 + single i j (δ a) := by
  ext k l
  simp only [coe_elemSL, Matrix.map_apply, Matrix.add_apply, Matrix.one_apply,
    Matrix.single_apply]
  split_ifs <;> simp

private theorem commute_single_of_fix0 {A : GL (Fin 3) F} {δ : F ≃+* F} (i j : Fin 3)
    (hij : i ≠ j)
    (h : (conjAut 3 F A * fieldAut 3 F δ) (proj 3 F (elemSL i j hij 1)) =
      proj 3 F (elemSL i j hij 1)) :
    Commute (single i j (1 : F)) (A : Matrix (Fin 3) (Fin 3) F) := by
  obtain ⟨c, hc3, hcm⟩ := fix0 h
  rw [map_coe_elemSL, map_one, coe_elemSL] at hcm
  have hcm' : (1 + single i j (1 : F) : Matrix (Fin 3) (Fin 3) F) =
      c • ((A : Matrix (Fin 3) (Fin 3) F) * (1 + single i j (1 : F)) *
        ((A⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)) := by
    exact hcm
  have ht := congrArg Matrix.trace hcm'
  rw [Matrix.trace_smul, Matrix.trace_units_conj] at ht
  simp [Matrix.trace_add, Matrix.trace_single_eq_of_ne i j _ hij] at ht
  have hc1 : c = 1 := eq_one_of_cube_of_three_mul hc3 (by rw [mul_comm]; exact ht.symm)
  rw [hc1, one_smul] at hcm'
  have h2 : (1 + single i j (1 : F) : Matrix (Fin 3) (Fin 3) F) *
      (A : Matrix (Fin 3) (Fin 3) F) =
      (A : Matrix (Fin 3) (Fin 3) F) * (1 + single i j (1 : F)) := by
    calc (1 + single i j (1 : F) : Matrix (Fin 3) (Fin 3) F) * (A : Matrix (Fin 3) (Fin 3) F)
        = ((A : Matrix (Fin 3) (Fin 3) F) * (1 + single i j (1 : F)) *
          ((A⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)) *
            (A : Matrix (Fin 3) (Fin 3) F) := by
          rw [← hcm']
      _ = _ := by rw [Matrix.mul_assoc, Units.inv_mul, Matrix.mul_one]
  have h3 := h2
  rw [add_mul, mul_add, Matrix.one_mul, Matrix.mul_one] at h3
  exact add_left_cancel h3

private theorem mem_range_scalar_of_fix0 {A : GL (Fin 3) F} {δ : F ≃+* F}
    (h : ∀ (i j : Fin 3) (hij : i ≠ j), (conjAut 3 F A * fieldAut 3 F δ)
      (proj 3 F (elemSL i j hij 1)) = proj 3 F (elemSL i j hij 1)) :
    (A : Matrix (Fin 3) (Fin 3) F) ∈ Set.range (Matrix.scalar (Fin 3)) :=
  Matrix.mem_range_scalar_of_commute_single fun i j hij =>
    commute_single_of_fix0 i j hij (h i j hij)

theorem conj_eq_of_mem_range_scalar {A : GL (Fin 3) F}
    (hA : (A : Matrix (Fin 3) (Fin 3) F) ∈ Set.range (Matrix.scalar (Fin 3)))
    (M : Matrix (Fin 3) (Fin 3) F) :
    (A : Matrix (Fin 3) (Fin 3) F) * M * ((A⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
      M := by
  obtain ⟨a, ha⟩ := hA
  have hc : (A : Matrix (Fin 3) (Fin 3) F) * M = M * (A : Matrix (Fin 3) (Fin 3) F) := by
    rw [← ha]
    exact Matrix.scalar_commute a (fun x => Commute.all _ _) M
  calc (A : Matrix (Fin 3) (Fin 3) F) * M * ((A⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)
      = M * (A : Matrix (Fin 3) (Fin 3) F) *
        ((A⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) := by
        rw [hc]
    _ = M := by rw [Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one]

private theorem fixes_of_fix0 {A : GL (Fin 3) F} {δ : F ≃+* F}
    (hA : (A : Matrix (Fin 3) (Fin 3) F) ∈ Set.range (Matrix.scalar (Fin 3)))
    (i j : Fin 3) (hij : i ≠ j) (a : F)
    (h : (conjAut 3 F A * fieldAut 3 F δ) (proj 3 F (elemSL i j hij a)) =
      proj 3 F (elemSL i j hij a)) : δ a = a := by
  obtain ⟨c, hc3, hcm⟩ := fix0 h
  rw [map_coe_elemSL, conj_eq_of_mem_range_scalar hA, coe_elemSL] at hcm
  have h1 := congrFun (congrFun hcm i) i
  have h2 := congrFun (congrFun hcm i) j
  simp [hij, hij.symm] at h1 h2
  rw [← h1, one_mul] at h2
  exact h2.symm

private theorem elemSL_inv (i j : Fin 3) (hij : i ≠ j) (a : F) :
    (elemSL i j hij a)⁻¹ = elemSL i j hij (-a) := by
  refine inv_eq_of_mul_eq_one_right (Subtype.ext ?_)
  have h0 : (single i j a * single i j (-a) : Matrix (Fin 3) (Fin 3) F) = 0 := by
    simp [hij.symm]
  have h1 : (single i j (-a) + single i j a : Matrix (Fin 3) (Fin 3) F) = 0 := by
    rw [← Matrix.single_add]; simp
  rw [Matrix.SpecialLinearGroup.coe_mul, coe_elemSL, coe_elemSL,
    Matrix.SpecialLinearGroup.coe_one, add_mul, mul_add, mul_add, h0]
  simp only [Matrix.one_mul, Matrix.mul_one, add_zero]
  rw [add_assoc, h1, add_zero]

private theorem std1_apply (A : GL (Fin 3) F) (δ : F ≃+* F)
    (g : Matrix.SpecialLinearGroup (Fin 3) F) :
    (conjAut 3 F A * fieldAut 3 F δ * dualAut 3 F) (proj 3 F g) =
      proj 3 F (CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation 3 F A
        (Matrix.SpecialLinearGroup.map δ.toRingHom (g⁻¹).transpose)) := by
  rw [MulAut.mul_apply, MulAut.mul_apply, dualAut_proj, fieldAut_proj, conjAut_proj]

private theorem coe_map_transpose_inv_elemSL (δ : F ≃+* F) (i j : Fin 3) (hij : i ≠ j) :
    ((Matrix.SpecialLinearGroup.map δ.toRingHom ((elemSL i j hij (1 : F))⁻¹).transpose :
      Matrix.SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
      1 + single j i (-1) := by
  rw [elemSL_inv, Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply,
    Matrix.SpecialLinearGroup.coe_transpose, coe_elemSL]
  rw [Matrix.transpose_add, Matrix.transpose_one, Matrix.transpose_single,
    Matrix.map_add _ (map_add δ.toRingHom),
    Matrix.map_one _ (map_zero _) (map_one _)]
  simp

private theorem rel_of_fix1 {A : GL (Fin 3) F} {δ : F ≃+* F} (i j : Fin 3) (hij : i ≠ j)
    (h : (conjAut 3 F A * fieldAut 3 F δ * dualAut 3 F) (proj 3 F (elemSL i j hij 1)) =
      proj 3 F (elemSL i j hij 1)) :
    (A : Matrix (Fin 3) (Fin 3) F) * single j i 1 =
      -(single i j 1 * (A : Matrix (Fin 3) (Fin 3) F)) := by
  rw [std1_apply] at h
  obtain ⟨c, hc3, hcm⟩ := exists_smul_of_proj_eq h
  have e1 : ((CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation 3 F A
      (Matrix.SpecialLinearGroup.map δ.toRingHom ((elemSL i j hij (1 : F))⁻¹).transpose) :
        Matrix.SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
      (A : Matrix (Fin 3) (Fin 3) F) * (1 + single j i (-1)) *
        ((A⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) := by
    rw [CFSG.LocalAnalysis.ComponentInitial.LinearFlag.coe_slConjugation,
      coe_map_transpose_inv_elemSL]
  rw [e1, coe_elemSL] at hcm
  have ht := congrArg Matrix.trace hcm
  rw [Matrix.trace_smul, Matrix.trace_units_conj] at ht
  simp [Matrix.trace_add, Matrix.trace_single_eq_of_ne i j _ hij,
    Matrix.trace_single_eq_of_ne j i _ hij.symm] at ht
  have hc1 : c = 1 := eq_one_of_cube_of_three_mul hc3 (by rw [mul_comm]; exact ht.symm)
  rw [hc1, one_smul] at hcm
  have h2 : (1 + single i j (1 : F) : Matrix (Fin 3) (Fin 3) F) *
      (A : Matrix (Fin 3) (Fin 3) F) =
      (A : Matrix (Fin 3) (Fin 3) F) * (1 + single j i (-1 : F)) := by
    calc (1 + single i j (1 : F) : Matrix (Fin 3) (Fin 3) F) * (A : Matrix (Fin 3) (Fin 3) F)
        = ((A : Matrix (Fin 3) (Fin 3) F) * (1 + single j i (-1 : F)) *
          ((A⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)) *
            (A : Matrix (Fin 3) (Fin 3) F) := by
          rw [← hcm]
      _ = _ := by rw [Matrix.mul_assoc, Units.inv_mul, Matrix.mul_one]
  rw [add_mul, mul_add, Matrix.one_mul, Matrix.mul_one] at h2
  have h3 := add_left_cancel h2
  rw [h3, ← Matrix.single_neg, mul_neg, neg_neg]

private theorem false_of_fix1 {A : GL (Fin 3) F} {δ : F ≃+* F}
    (h : ∀ (i j : Fin 3) (hij : i ≠ j), (conjAut 3 F A * fieldAut 3 F δ * dualAut 3 F)
      (proj 3 F (elemSL i j hij 1)) = proj 3 F (elemSL i j hij 1)) : False := by
  have R := fun i j hij => rel_of_fix1 (A := A) (δ := δ) i j hij (h i j hij)
  have key : ∀ (i j : Fin 3) (hij : i ≠ j), (A : Matrix (Fin 3) (Fin 3) F) * single j j 1 =
      single i i 1 * (A : Matrix (Fin 3) (Fin 3) F) := by
    intro i j hij
    have h1 := R i j hij
    have h2 := R j i hij.symm
    calc (A : Matrix (Fin 3) (Fin 3) F) * single j j (1 : F)
        = (A : Matrix (Fin 3) (Fin 3) F) * (single j i (1 : F) * single i j (1 : F)) := by simp
      _ = ((A : Matrix (Fin 3) (Fin 3) F) * single j i (1 : F)) * single i j (1 : F) := by
          rw [Matrix.mul_assoc]
      _ = -(single i j (1 : F) * (A : Matrix (Fin 3) (Fin 3) F)) * single i j (1 : F) := by
          rw [h1]
      _ = -(single i j (1 : F) * ((A : Matrix (Fin 3) (Fin 3) F) * single i j (1 : F))) := by
          rw [neg_mul, Matrix.mul_assoc]
      _ = -(single i j (1 : F) * (-(single j i (1 : F) * (A : Matrix (Fin 3) (Fin 3) F)))) := by
          rw [h2]
      _ = (single i j (1 : F) * single j i (1 : F)) * (A : Matrix (Fin 3) (Fin 3) F) := by
          rw [mul_neg, neg_neg, Matrix.mul_assoc]
      _ = single i i 1 * (A : Matrix (Fin 3) (Fin 3) F) := by simp
  have k1 := key 1 0 (by decide)
  have k2 := key 2 0 (by decide)
  have h12 : (single (1 : Fin 3) (1 : Fin 3) (1 : F)) * (A : Matrix (Fin 3) (Fin 3) F) =
      single (2 : Fin 3) (2 : Fin 3) (1 : F) * (A : Matrix (Fin 3) (Fin 3) F) := k1.symm.trans k2
  have h3 : (single (1 : Fin 3) (1 : Fin 3) (1 : F)) = single (2 : Fin 3) (2 : Fin 3) (1 : F) := by
    calc (single (1 : Fin 3) (1 : Fin 3) (1 : F))
        = single (1 : Fin 3) (1 : Fin 3) (1 : F) * (A : Matrix (Fin 3) (Fin 3) F) *
          ((A⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) := by
          rw [Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one]
      _ = single (2 : Fin 3) (2 : Fin 3) (1 : F) * (A : Matrix (Fin 3) (Fin 3) F) *
          ((A⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) := by rw [h12]
      _ = single (2 : Fin 3) (2 : Fin 3) (1 : F) := by
          rw [Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one]
  have h4 := congrFun (congrFun h3 1) 1
  simp at h4

theorem eq_one_of_fix_fixedField [Finite F] {ψ δ : F ≃+* F} (hodd : Odd (orderOf ψ))
    (hfix : ∀ a ∈ fixedField ψ, δ a = a) {m : ℕ} (hδ : δ ^ 2 ^ m = 1) : δ = 1 := by
  classical
  have : Fintype (Subgroup.zpowers ψ) := Fintype.ofFinite _
  have : IsGalois (fixedField ψ) F := IsGalois.of_fixed_field F (Subgroup.zpowers ψ)
  have : FiniteDimensional (fixedField ψ) F := inferInstance
  have hrank : Module.finrank (fixedField ψ) F = orderOf ψ := by
    have h := FixedPoints.finrank_eq_card (Subgroup.zpowers ψ) F
    rw [Fintype.card_eq_nat_card, Nat.card_zpowers] at h
    exact h
  let δ' : F ≃ₐ[fixedField ψ] F := AlgEquiv.ofRingEquiv (f := δ) (fun x => hfix x x.2)
  have hpow : ∀ k : ℕ, (δ' ^ k).toRingEquiv = δ ^ k := by
    intro k
    induction k with
    | zero => rfl
    | succ k ih => rw [pow_succ, pow_succ, ← ih]; rfl
  have h1 : δ' ^ orderOf ψ = 1 := by
    rw [← hrank, ← IsGalois.card_aut_eq_finrank (fixedField ψ) F]
    exact pow_card_eq_one'
  have h2 : δ' ^ 2 ^ m = 1 := by
    apply AlgEquiv.toRingEquiv_injective
    rw [hpow, hδ]
    rfl
  have h3 : δ' ^ Nat.gcd (orderOf ψ) (2 ^ m) = 1 := pow_gcd_eq_one.mpr ⟨h1, h2⟩
  have hg : Nat.gcd (orderOf ψ) (2 ^ m) = 1 :=
    Nat.Coprime.pow_right m (Nat.coprime_two_right.mpr hodd)
  rw [hg, pow_one] at h3
  have h4 : δ'.toRingEquiv = (1 : F ≃ₐ[fixedField ψ] F).toRingEquiv := by rw [h3]
  exact h4

private theorem fieldAut_injective : Function.Injective (fieldAut 3 F) := by
  rw [injective_iff_map_eq_one]
  intro ε hε
  ext a
  exact fixes_of_fix0 (A := 1) (δ := ε) ⟨1, by simp⟩ 0 1 (by decide) a
    (by rw [map_one, one_mul, hε]; rfl)

private theorem proj_elemSL_mem_range_linFix (ψ : F ≃+* F) (i j : Fin 3) (hij : i ≠ j) {a : F}
    (ha : a ∈ fixedField ψ) : proj 3 F (elemSL i j hij a) ∈ (linFix ψ).range := by
  refine ⟨elemSL i j hij (⟨a, ha⟩ : fixedField ψ), ?_⟩
  show proj 3 F (Matrix.SpecialLinearGroup.map (fixedField ψ).subtype
    (elemSL i j hij (⟨a, ha⟩ : fixedField ψ))) = _
  congr 1
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply, coe_elemSL, coe_elemSL]
  rw [Matrix.map_add _ (map_add _), Matrix.map_one _ (map_zero _) (map_one _)]
  congr 1
  ext k l
  simp only [Matrix.map_apply, Matrix.single_apply]
  split_ifs <;> rfl

private theorem conjAut_eq_one_of_mem_range_scalar {A : GL (Fin 3) F}
    (hA : (A : Matrix (Fin 3) (Fin 3) F) ∈ Set.range (Matrix.scalar (Fin 3))) :
    conjAut 3 F A = 1 := by
  ext x
  obtain ⟨g, rfl⟩ := proj_surjective 3 F x
  rw [conjAut_proj, MulAut.one_apply]
  congr 1
  apply Subtype.ext
  rw [CFSG.LocalAnalysis.ComponentInitial.LinearFlag.coe_slConjugation]
  exact conj_eq_of_mem_range_scalar hA _

theorem linear_model_eq_one [Finite F] {ψ : F ≃+* F} (hodd : Odd (orderOf ψ))
    {t : MulAut (projectiveSL 3 F)} (ht : ∃ m : ℕ, t ^ 2 ^ m = 1)
    (hfix : ∀ x ∈ (linFix ψ).range, t x = x) : t = 1 := by
  obtain ⟨m, hm⟩ := ht
  obtain ⟨A, δ, ε, hε, hform⟩ := (automorphism_generation (K := F) (n := 3) le_rfl).2 t
  have hfixe : ∀ (i j : Fin 3) (hij : i ≠ j) (a : F), a ∈ fixedField ψ →
      t (proj 3 F (elemSL i j hij a)) = proj 3 F (elemSL i j hij a) :=
    fun i j hij a ha => hfix _ (proj_elemSL_mem_range_linFix ψ i j hij ha)
  interval_cases ε
  · rw [pow_zero, mul_one] at hform
    have hfix0 : ∀ (i j : Fin 3) (hij : i ≠ j) (a : F), a ∈ fixedField ψ →
        (conjAut 3 F A * fieldAut 3 F δ) (proj 3 F (elemSL i j hij a)) =
          proj 3 F (elemSL i j hij a) := by
      intro i j hij a ha
      rw [← hform]
      exact hfixe i j hij a ha
    have hA := mem_range_scalar_of_fix0 (fun i j hij => hfix0 i j hij 1 (one_mem _))
    have hδ : ∀ a ∈ fixedField ψ, δ a = a := fun a ha =>
      fixes_of_fix0 hA 0 1 (by decide) a (hfix0 0 1 (by decide) a ha)
    have ht' : t = fieldAut 3 F δ := by
      rw [hform, conjAut_eq_one_of_mem_range_scalar hA, one_mul]
    have hδm : δ ^ 2 ^ m = 1 := by
      apply fieldAut_injective
      rw [map_pow, ← ht', map_one]
      exact hm
    rw [ht', eq_one_of_fix_fixedField hodd hδ hδm, map_one]
  · exfalso
    rw [pow_one] at hform
    exact false_of_fix1 (fun i j hij => by
      rw [← hform]
      exact hfixe i j hij 1 (one_mem _))

theorem noTwoCentAut_of_eq_comap {S : Type} [Group S] {K : Subgroup S} {F : Type} [Field F]
    [Finite F] (τ : S ≃* projectiveSL 3 F) {ψ : F ≃+* F} (hψodd : Odd (orderOf ψ))
    (hKeq : K = (linFix ψ).range.comap τ.toMonoidHom) : NoTwoCentAut K := by
  intro t ⟨m, hm⟩ hfix
  have h1 : ∀ x ∈ (linFix ψ).range, MulAut.congr τ t x = x := by
    intro x hx
    have hmem : τ.symm x ∈ K := by
      rw [hKeq]
      simpa using hx
    show τ (t (τ.symm x)) = x
    rw [hfix _ hmem]
    simp
  have h2 : (MulAut.congr τ t) ^ 2 ^ m = 1 := by rw [← map_pow, hm, map_one]
  have h3 := linear_model_eq_one hψodd ⟨m, h2⟩ h1
  exact (MulAut.congr τ).injective (by rw [h3, map_one])

theorem exists_iso_fieldAut {S : Type} [Group S] {σ : MulAut S} {F : Type} [Field F]
    (e : S ≃* projectiveSL 3 F) (hk : (stdPinnedPSL 3 F).HasKind (MulAut.congr e σ) .field) :
    ∃ (τ : S ≃* projectiveSL 3 F) (ψ : F ≃+* F), ψ ≠ 1 ∧ MulAut.congr τ σ = fieldAut 3 F ψ := by
  obtain ⟨φ, hφ, hφ1, d, hd, hσ⟩ := hk
  rw [stdPinnedPSL_field] at hφ
  rw [stdPinnedPSL_inndiag, linearAutGroup_eq_range] at hd
  obtain ⟨ψ, rfl⟩ := hφ
  obtain ⟨H, rfl⟩ := hd
  refine ⟨e.trans (conjAut 3 F H)⁻¹, ψ, fun h1 => hφ1 (by rw [h1, map_one]), ?_⟩
  have : MulAut.congr (e.trans (conjAut 3 F H)⁻¹) σ =
      (conjAut 3 F H)⁻¹ * MulAut.congr e σ * ((conjAut 3 F H)⁻¹)⁻¹ := by
    ext y
    rfl
  rw [this, hσ]
  group

theorem noTwoCentAut_of_field_linear {S : Type} [Group S] [Finite S] {σ : MulAut S}
    {K : Subgroup S} (hK : K ≤ Sec4.autFix σ) [Group.IsPerfect K] (hnt : K ≠ ⊥)
    (hsub : (K.subgroupOf (Sec4.autFix σ)).IsSubnormal) (hodd : Odd (orderOf σ))
    {F : Type} [Field F] [Finite F] (e : S ≃* projectiveSL 3 F)
    (hk : (stdPinnedPSL 3 F).HasKind (MulAut.congr e σ) .field) : NoTwoCentAut K := by
  obtain ⟨τ, ψ, -, hστ⟩ := exists_iso_fieldAut e hk
  have hψodd : Odd (orderOf ψ) := by
    rw [← orderOf_injective (fieldAut 3 F) fieldAut_injective ψ, ← hστ,
      MulEquiv.orderOf_eq (MulAut.congr τ) σ]
    exact hodd
  exact noTwoCentAut_of_eq_comap τ hψodd
    (eq_comap_range_linFix τ hστ (fun x => Iff.rfl) hK hnt hsub)

end Linear

end CFSG.RankThree.PartTwo.Sec15.Liebeck155R1L3T150
