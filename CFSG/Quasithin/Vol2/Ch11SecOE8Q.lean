module

public import CFSG.LocalAnalysis.ComponentClassification.OutcomeLocalCTIUnitarySocleForms
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_7FinMaxL3Fix

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecE3.Lie3

namespace L3T

open Matrix CFSG.Open CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag CFSG.LocalAnalysis.ComponentInitial.LinearFieldFour
  CFSG.QuasithinUnique.Fin257 CFSG.QuasithinUnique.Fin257.L3 FourGroupEvenCanonical
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.ComponentClassification.CatalogueBAlternatingIsometry (exists_planeIsometryEquivSL)
open CFSG.ComponentClassification.OutcomeLocal (dotForm_restrict_isAlt
  dotForm_restrict_nondegenerate finrank_dotForm_ker oneRestrictEquiv)
open scoped MatrixGroups

theorem card_SL_two {k : Type*} [Field k] [Finite k] :
    Nat.card SL(2, k) = Nat.card k * (Nat.card k ^ 2 - 1) := by
  classical
  have := Fintype.ofFinite k
  have h := Matrix.card_SL_mul_card_units (n := Fin 2) (R := k)
  rw [Matrix.card_GL_field, Fin.prod_univ_two, Nat.card_units] at h
  simp only [Fin.val_zero, Fin.val_one, pow_zero, pow_one] at h
  rw [← Nat.card_eq_fintype_card] at h
  set q := Nat.card k
  have hq : 2 ≤ q := Finite.one_lt_card
  apply Nat.eq_of_mul_eq_mul_right (show 0 < q - 1 by omega)
  rw [h, show q ^ 2 - q = q * (q - 1) by rw [Nat.mul_sub_one, ← pow_two]]
  ring

section Delta

variable (F : Type) [Field F] [CharP F 2]

@[expose] def orthSL :
    matrixIsometryGroup ((1 : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) →* SL(3, F) where
  toFun g := ⟨(g : GL (Fin 3) F), det_eq_one_of_mem (by simp) g.2⟩
  map_one' := rfl
  map_mul' _ _ := rfl

@[expose] def orthProj :
    matrixIsometryGroup ((1 : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) →* projectiveSL 3 F :=
  (proj 3 F).comp (orthSL F)

variable {F}

theorem coe_orthSL (g : matrixIsometryGroup ((1 : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)) :
    ((orthSL F g : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) =
      ((g : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) :=
  rfl

omit [CharP F 2] in
theorem mem_orth_iff {g : GL (Fin 3) F} :
    g ∈ matrixIsometryGroup ((1 : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) ↔
      (g : Matrix (Fin 3) (Fin 3) F)ᵀ * g = 1 := by
  rw [mem_matrixIsometryGroup, Units.val_one, Matrix.mul_one]

theorem orthProj_injective : Function.Injective (orthProj F) := by
  rw [injective_iff_map_eq_one]
  intro g hg
  rw [orthProj, MonoidHom.comp_apply, proj_eq_one_iff] at hg
  obtain ⟨c, hc3, hgc⟩ := mem_scalars.1 hg
  rw [coe_orthSL] at hgc
  have horth := mem_orth_iff.1 g.2
  rw [hgc, scalar_apply, diagonal_transpose, diagonal_mul_diagonal] at horth
  have hc2 : (c : F) * c = 1 := by
    have := congrFun (congrFun horth 0) 0
    simpa using this
  have hc1 : c = 1 := by
    have h2 : c ^ 2 = 1 := Units.ext (by rw [Units.val_pow_eq_pow_val, sq, hc2, Units.val_one])
    calc c = c ^ 3 * (c ^ 2)⁻¹ := by group
      _ = 1 := by rw [hc3, h2, inv_one, one_mul]
  apply Subtype.ext
  apply Units.ext
  rw [hgc, hc1, Units.val_one, map_one]
  rfl

theorem range_orthProj : (orthProj F).range = fixedSubgroup (dualAut 3 F) := by
  ext x
  constructor
  · rintro ⟨g, rfl⟩
    change dualAut 3 F (proj 3 F (orthSL F g)) = proj 3 F (orthSL F g)
    rw [dualAut_proj]
    congr 1
    apply Subtype.ext
    have horth := mem_orth_iff.1 g.2
    rw [Matrix.SpecialLinearGroup.coe_transpose, coe_orthSL]
    have hinv : ((orthSL F g)⁻¹ : SL(3, F)) = (orthSL F g).transpose := by
      refine inv_eq_of_mul_eq_one_right (Subtype.ext ?_)
      rw [Matrix.SpecialLinearGroup.coe_mul (orthSL F g),
        Matrix.SpecialLinearGroup.coe_transpose, coe_orthSL, Matrix.SpecialLinearGroup.coe_one]
      exact mul_eq_one_comm.1 horth
    rw [hinv, Matrix.SpecialLinearGroup.coe_transpose, coe_orthSL, transpose_transpose]
  · intro hx
    obtain ⟨A, rfl⟩ := proj_surjective 3 F x
    change dualAut 3 F (proj 3 F A) = proj 3 F A at hx
    rw [dualAut_proj, proj_eq_proj_iff] at hx
    obtain ⟨c, hc3, hAc⟩ := mem_scalars.1 hx
    have hT : ((A⁻¹ : SL(3, F)).transpose)⁻¹ = A.transpose := by
      refine inv_eq_of_mul_eq_one_right (Subtype.ext ?_)
      rw [Matrix.SpecialLinearGroup.coe_mul A⁻¹.transpose, Matrix.SpecialLinearGroup.coe_transpose,
        Matrix.SpecialLinearGroup.coe_transpose, ← transpose_mul,
        ← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel, Matrix.SpecialLinearGroup.coe_one,
        transpose_one]
    have hAc' : (A : Matrix (Fin 3) (Fin 3) F)ᵀ * A = scalar (Fin 3) (c : F) := by
      rw [← hAc, hT, Matrix.SpecialLinearGroup.coe_mul A.transpose,
        Matrix.SpecialLinearGroup.coe_transpose]
    clear hAc
    set B : SL(3, F) := scalarElement c hc3 * A with hB
    have hBm : (B : Matrix (Fin 3) (Fin 3) F) = scalar (Fin 3) (c : F) * A := rfl
    have hc3' : (c : F) * c * c = 1 := by
      have := congrArg Units.val hc3
      simpa [pow_succ] using this
    have hsc : scalar (Fin 3) (c : F) = (c : F) • (1 : Matrix (Fin 3) (Fin 3) F) := by
      rw [scalar_apply, smul_one_eq_diagonal]
    have hBorth : (B : Matrix (Fin 3) (Fin 3) F)ᵀ * B = 1 := by
      rw [hBm, hsc, smul_mul, Matrix.one_mul, transpose_smul, smul_mul, Matrix.mul_smul, hAc',
        hsc, smul_smul, smul_smul, hc3', one_smul]
    refine ⟨⟨Matrix.SpecialLinearGroup.toGL B, mem_orth_iff.2 hBorth⟩, ?_⟩
    change proj 3 F (orthSL F _) = proj 3 F A
    have hBB : orthSL F ⟨Matrix.SpecialLinearGroup.toGL B, mem_orth_iff.2 hBorth⟩ = B :=
      Subtype.ext rfl
    rw [hBB, hB, map_mul, proj_eq_one_iff.2 (scalarElement_mem_scalars c hc3), one_mul]

theorem exists_SL_two_fixed_dualAut :
    ∃ j : SL(2, F) →* projectiveSL 3 F,
      Function.Injective j ∧ j.range = fixedSubgroup (dualAut 3 F) := by
  have h3 : (3 : ℕ) = 2 * 1 + 1 := rfl
  obtain ⟨eSL⟩ := exists_planeIsometryEquivSL _ (dotForm_restrict_isAlt (k := F) (n := 3))
    (dotForm_restrict_nondegenerate h3) (finrank_dotForm_ker h3)
  set e := (oneRestrictEquiv (k := F) h3).trans eSL
  refine ⟨(orthProj F).comp e.symm.toMonoidHom, orthProj_injective.comp e.symm.injective, ?_⟩
  rw [MonoidHom.range_comp, MonoidHom.range_eq_top.2 e.symm.surjective, Subgroup.map_top,
    range_orthProj]

end Delta

section Graph

variable {F : Type} [Field F] [CharP F 2]

theorem eq_one_of_fix_Wg {A : GL (Fin 3) F} {σ : F ≃+* F}
    (hfix : ∀ c : F,
      (LinearFlag.conjAut 3 F A * fieldAut 3 F σ * dualAut 3 F ^ 1) (wP c) = wP c) :
    σ = 1 := by
  have hinv : ∀ c : F, ((wMat c)⁻¹ : SL(3, F)) = wMat c := fun c =>
    inv_eq_of_mul_eq_one_right (by rw [← wMat_add, CharTwo.add_self_eq_zero, wMat_zero])
  have key : ∀ c : F, (A : Matrix (Fin 3) (Fin 3) F) * (wM c).transpose.map σ =
      wM c * (A : Matrix (Fin 3) (Fin 3) F) := by
    intro c
    have h1 := standard_apply_proj A σ 1 (wMat c)
    have h2 : proj 3 F (Phi A σ 1 (wMat c)) = proj 3 F (wMat c) := by
      rw [← h1]
      exact hfix c
    have hw2 : wMat c * wMat c = 1 := by rw [← wMat_add, CharTwo.add_self_eq_zero, wMat_zero]
    have h3 : Phi A σ 1 (wMat c) = wMat c := by
      refine eq_of_proj_eq_of_sq ?_ hw2 h2
      rw [← map_mul, hw2, map_one]
    have h4 := congrArg (fun x : SL(3, F) => (x : Matrix (Fin 3) (Fin 3) F)) h3
    simp only [coe_Phi_one, hinv, coe_wMat] at h4
    exact mul_eq_of_phi h4
  have E1 := key 1
  have f10 := congrFun (congrFun E1 1) 0
  have f20 := congrFun (congrFun E1 2) 0
  have f21 := congrFun (congrFun E1 0) 1
  have f00 := congrFun (congrFun E1 0) 0
  simp [wM, Matrix.mul_apply, Fin.sum_univ_three, Matrix.map_apply] at f10 f20 f21 f00
  have hA02 : (A : Matrix (Fin 3) (Fin 3) F) 0 2 ≠ 0 := by
    intro h0
    apply det_ne_zero A
    rw [Matrix.det_fin_three, h0, f10, f20]
    ring
  refine RingEquiv.ext fun c => ?_
  have g00 := congrFun (congrFun (key c) 0) 0
  simp [wM, Matrix.mul_apply, Fin.sum_univ_three, Matrix.map_apply] at g00
  have h' : (σ c - c) * (A : Matrix (Fin 3) (Fin 3) F) 0 2 = 0 := by
    linear_combination g00 - c * f00
  exact sub_eq_zero.mp ((mul_eq_zero.mp h').resolve_right hA02)

theorem exists_SL_two_fixed_of_twisted [Finite F] {f : ℕ} (hf : 1 ≤ f) (hF : Nat.card F = 2 ^ f)
    {a : MulAut (projectiveSL 3 F)} (ha2 : a * a = 1) (haE : a ∉ semilinearAutGroup 3 F)
    (hfix : ∀ g ∈ (Wg : Subgroup (projectiveSL 3 F)), a g = g) :
    ∃ j : SL(2, F) →* projectiveSL 3 F, Function.Injective j ∧ j.range = fixedSubgroup a := by
  obtain ⟨-, hform⟩ := automorphism_generation (K := F) (n := 3) le_rfl
  obtain ⟨A, σ, ε, hε, rfl⟩ := hform a
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hε with rfl | rfl
  · exfalso
    apply haE
    rw [pow_zero, mul_one]
    exact mem_semilinearAutGroup_iff.mpr ⟨A, σ, rfl⟩
  have hσ : σ = 1 := eq_one_of_fix_Wg fun c => hfix (wP c) ⟨c, rfl⟩
  subst hσ
  rw [map_one, mul_one, pow_one] at ha2 ⊢
  have ha2' : (LinearFlag.conjAut 3 F A * dualAut 3 F) ^ 2 = 1 := by rw [pow_two]; exact ha2
  obtain ⟨-, ⟨H, C, -, hβ, hC⟩, -⟩ :=
    UnitaryHigher.even_linear_pure_graph_involution_normal_forms hf hF le_rfl A ha2'
  rcases hC with ⟨h1C, -⟩ | ⟨r, hr, -, -⟩
  swap
  · omega
  have hC1 : C = 1 := Units.ext h1C
  rw [hC1, map_one, one_mul] at hβ
  obtain ⟨j, hj, hjr⟩ := exists_SL_two_fixed_dualAut (F := F)
  set γ := LinearFlag.conjAut 3 F H with hγ
  refine ⟨(γ : projectiveSL 3 F →* projectiveSL 3 F).comp j, γ.injective.comp hj, ?_⟩
  rw [MonoidHom.range_comp, hjr, hβ]
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    have hy' : dualAut 3 F y = y := hy
    change (γ * dualAut 3 F * γ⁻¹) (γ y) = γ y
    rw [MulAut.mul_apply, MulAut.mul_apply, MulAut.inv_apply_self, hy']
  · intro hx
    have hx' : (γ * dualAut 3 F * γ⁻¹) x = x := hx
    refine ⟨γ⁻¹ x, ?_, by simp⟩
    change dualAut 3 F (γ⁻¹ x) = γ⁻¹ x
    rw [MulAut.mul_apply, MulAut.mul_apply] at hx'
    calc dualAut 3 F (γ⁻¹ x) = γ⁻¹ (γ (dualAut 3 F (γ⁻¹ x))) := (MulAut.inv_apply_self _ γ _).symm
      _ = γ⁻¹ x := by rw [hx']

end Graph

end L3T

end CFSG.Quasithin.Vol2.Ch11.SecE3.Lie3
