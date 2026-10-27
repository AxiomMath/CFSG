module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X7SecGroup
public import CFSG.LocalAnalysis.ComponentInitial.LinearFieldFourRoots
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBGraphFieldAction
public import CFSG.Fischer.Classification.Basic.Heisenberg
public import CFSG.Quasithin.Background.GoldschmidtG22M12IdentLinear
public import CFSG.Quasithin.Background.VolIExtraspecialRank
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X7bGamma
import CFSG.LocalAnalysis.RankThreeUC.GN15FFOLinkPSLAut

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Thm14_2

open CFSG.Quasithin CFSG.Open
open CFSG.LocalAnalysis.ComponentInitial CFSG.QuasithinUnique.Setup
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag CFSG.Fischer.Classification
open scoped MatrixGroups Matrix commutatorElement

section Rep
variable {F : Type} [Field F] [Fintype F] [CharP F 2]
  {U : Type} [AddCommGroup U] [Module (ZMod 2) U] [Finite U]

private noncomputable def graphFieldFrob : F ≃+* F :=
  CFSG.LieType.BorelTits.unitaryInvolution F 2 1

private lemma graphFieldFrob_apply (c : F) : graphFieldFrob (F := F) c = c ^ 2 := by
  rw [graphFieldFrob, CFSG.LieType.BorelTits.unitaryInvolution_apply]
  norm_num

private lemma frobPow_eq_frobSL_of_odd (hF : Fintype.card F = 2 ^ 2) {j : ℕ} (hj : Odd j) :
    X7a.frobPow F j = X7a.frobSL F := by
  obtain ⟨t, rfl⟩ := hj
  have h2 : ∀ g : SL(3, F), (X7a.frobSL F)^[2] g = g := fun g => by
    simpa using X7a.frobSL_iterate_card (F := F) (f := 2) hF g
  apply MonoidHom.ext
  intro g
  rw [X7Sec.frobPow_eq_iterate]
  induction t generalizing g with
  | zero => rfl
  | succ t ih =>
      rw [show 2 * (t + 1) + 1 = (2 * t + 1) + 2 by ring, Function.iterate_add_apply, h2, ih]

private lemma frobSL_eq_slFieldAut (x : SL(3, F)) :
    X7a.frobSL F x =
      CFSG.ComponentClassification.CatalogueBHigherLinearField.slFieldAut
        (Fin 3) F graphFieldFrob x := by
  apply Subtype.ext
  show (x.val.map (fun y : F => y ^ 2)) =
    (CFSG.ComponentClassification.CatalogueBHigherLinearField.slFieldEquiv
      (Fin 3) graphFieldFrob x).val
  ext i j
  rw [Matrix.map_apply,
    CFSG.ComponentClassification.CatalogueBHigherLinearField.slFieldEquiv_entry]
  simp [graphFieldFrob_apply]

private lemma tauSL_eq_slGraphAut (x : SL(3, F)) :
    X7a.tauSL F x = CFSG.ComponentClassification.CatalogueBGraphForm.slGraphAut 3 F x := by
  apply Subtype.ext
  show (X7a.tauSL F x).val =
    (CFSG.ComponentClassification.CatalogueBGraphForm.slGraphAut 3 F x).val
  rw [X7a.tauSL_coe, CFSG.ComponentClassification.CatalogueBGraphForm.slGraphAut_matrix]
  rfl

private lemma graphFieldHom_eq_stdAut (hF : Fintype.card F = 2 ^ 2) {j : ℕ} (hj : Odd j)
    (A : GL (Fin 3) F) :
    X7Sec.graphFieldHom A j =
      (CFSG.QuasithinUnique.K1.stdAut A graphFieldFrob 1 : SL(3, F) →* SL(3, F)) := by
  apply MonoidHom.ext
  intro x
  rw [X7Sec.graphFieldHom, frobPow_eq_frobSL_of_odd hF hj]
  change CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation 3 F A
      (X7a.tauSL F (X7a.frobSL F x)) =
    (CFSG.QuasithinUnique.K1.stdAut A graphFieldFrob 1 : MulAut (SL(3, F))) x
  rw [tauSL_eq_slGraphAut, frobSL_eq_slFieldAut,
    CFSG.ComponentClassification.CatalogueBGraphForm.slGraphAut_field_commute]
  rfl

private lemma mulAut_comp_self_eq_id {j : ℕ}
    (ρ : Representation (ZMod 2) SL(3, F) U)
    (hker : ∀ x : SL(3, F), ρ x = 1 → x ∈ LinearFlag.scalars 3 F)
    (a : U ≃ₗ[ZMod 2] U) (ha2 : a * a = 1) (A : GL (Fin 3) F)
    (hb : ∀ x : SL(3, F), X7a.Intertwines ρ a x (X7Sec.graphFieldHom A j x))
    (al : MulAut (SL(3, F)))
    (hstd : ∀ x : SL(3, F), X7Sec.graphFieldHom A j x = al x) :
    ∀ x : SL(3, F), al (al x) = x := by
  classical
  haveI : Group.IsPerfect (SL(3, F)) :=
    CFSG.LinearGroups.special_linear_dimension_at_least_three_perfect (K := F) (n := 3) le_rfl
  have hint : ∀ x : SL(3, F), X7a.Intertwines ρ a x (al x) := by
    intro x u
    have h := hb x u
    rwa [hstd x] at h
  have haa : ∀ u : U, a (a u) = u := fun u => by
    have h := congrArg (fun e : U ≃ₗ[ZMod 2] U => e u) ha2
    simpa using h
  have hpoint : ∀ y : SL(3, F), ∀ u : U, ρ (al (al y)) u = ρ y u := by
    intro y u
    have h1 := hint (al y) (a u)
    have h2 := hint y u
    rw [← h2] at h1
    rw [haa (ρ y u), haa u] at h1
    exact h1.symm
  have hcentral : ∀ y : SL(3, F), y⁻¹ * (al (al y)) ∈ Subgroup.center (SL(3, F)) := by
    intro y
    have hρ : ρ ((al (al y)) * y⁻¹) = 1 := by
      rw [map_mul]
      have hfun : ρ (al (al y)) = ρ y := LinearMap.ext (fun u => hpoint y u)
      rw [hfun, ← map_mul, mul_inv_cancel, map_one]
    have hscal := hker _ hρ
    have hcen : (al (al y)) * y⁻¹ ∈ Subgroup.center (SL(3, F)) :=
      LinearFlag.scalars_le_center 3 F hscal
    have hcomm := Subgroup.mem_center_iff.mp hcen y
    have hEq : y⁻¹ * (al (al y)) = (al (al y)) * y⁻¹ := by
      calc y⁻¹ * (al (al y)) = y⁻¹ * (((al (al y)) * y⁻¹) * y) := by group
        _ = y⁻¹ * (y * ((al (al y)) * y⁻¹)) := by rw [hcomm]
        _ = (al (al y)) * y⁻¹ := by group
    rw [hEq]
    exact hcen
  have hγ := CFSG.ComponentClassification.PerfectAutomorphisms.hom_eq_id_of_central_displacement
    ((al * al : MulAut (SL(3, F))) : SL(3, F) →* SL(3, F)) hcentral
  intro x
  have hx := DFunLike.congr_fun hγ x
  simpa [MulAut.mul_apply] using hx

private lemma fr_ne_one (hF4 : Nat.card F = 4) : graphFieldFrob (F := F) ≠ 1 := by
  obtain ⟨ω, hω0, hω1⟩ := LinearFieldFour.exists_ne_zero_ne_one hF4
  intro h
  have h1 : graphFieldFrob (F := F) ω = ω := by rw [h]; rfl
  rw [graphFieldFrob_apply] at h1
  have h2 : ω = 1 := by
    apply mul_left_cancel₀ hω0
    rw [← pow_two, h1, mul_one]
  exact hω1 h2

private lemma psl_sq_eq_one (A : GL (Fin 3) F) (al : MulAut (SL(3, F)))
    (hal : al = CFSG.QuasithinUnique.K1.stdAut A graphFieldFrob 1)
    (hα2 : ∀ x : SL(3, F), al (al x) = x) :
    (conjAut 3 F A * fieldAut 3 F graphFieldFrob * dualAut 3 F) ^ 2 = 1 := by
  have hdesc : descendAut 3 F al = conjAut 3 F A * fieldAut 3 F graphFieldFrob * dualAut 3 F := by
    rw [hal]
    exact CFSG.QuasithinUnique.K1.descendAut_stdAut A graphFieldFrob 1
  have hsq : al ^ 2 = 1 := by
    apply MulEquiv.ext
    intro x
    simpa [pow_two, MulAut.mul_apply] using hα2 x
  rw [← hdesc, ← map_pow, hsq, map_one]

private lemma descendAut_slGraphFieldAut :
    descendAut 3 F
        (CFSG.ComponentClassification.CatalogueBGraphField.slGraphFieldAut 3 F graphFieldFrob) =
      fieldAut 3 F graphFieldFrob * dualAut 3 F := by
  rw [CFSG.ComponentClassification.CatalogueBGraphField.slGraphFieldAut]
  simp only [map_mul]
  rfl

private lemma exists_conjugating_H (hF : Fintype.card F = 2 ^ 2)
    (A : GL (Fin 3) F) (al : MulAut (SL(3, F)))
    (hal : al = CFSG.QuasithinUnique.K1.stdAut A graphFieldFrob 1)
    (hα2 : ∀ x : SL(3, F), al (al x) = x) :
    ∃ H : GL (Fin 3) F,
      al = (CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation 3 F H) *
        (CFSG.ComponentClassification.CatalogueBGraphField.slGraphFieldAut 3 F graphFieldFrob) *
        (CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation 3 F H)⁻¹ := by
  have hF4 : Nat.card F = 4 := by
    rw [Nat.card_eq_fintype_card, hF]
    norm_num
  have hfr : graphFieldFrob (F := F) ≠ 1 := fr_ne_one hF4
  have hPSL2 := psl_sq_eq_one A al hal hα2
  obtain ⟨-, -, H, hH⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.LinearFlag.odd_linear_graph_field_involution_conjugacy
      (n := 3) (K := F) (p := 2) (f := 2) Nat.prime_two (by norm_num)
      (by rw [Nat.card_eq_fintype_card, hF]) (by norm_num) A graphFieldFrob hfr hPSL2
  refine ⟨H, ?_⟩
  apply CFSG.Quasithin.F6.G22M12Ident.descendAut_injective_three
  rw [show descendAut 3 F al = conjAut 3 F A * fieldAut 3 F graphFieldFrob * dualAut 3 F from by
    rw [hal]; exact CFSG.QuasithinUnique.K1.descendAut_stdAut A graphFieldFrob 1]
  simp only [map_mul, map_inv]
  rw [descendAut_slGraphFieldAut]
  exact hH

private def graphFieldDiagMat (ω : F) : Matrix (Fin 3) (Fin 3) F :=
  !![1, 0, 0; 0, ω, 0; 0, 0, ω ^ 2]
private def graphFieldPermMat : Matrix (Fin 3) (Fin 3) F := !![0, 0, 1; 1, 0, 0; 0, 1, 0]

private lemma graphFieldDiagMat_det (ω : F) (hω3 : ω ^ 3 = 1) : (graphFieldDiagMat ω).det = 1 := by
  simp [graphFieldDiagMat, Matrix.det_fin_three]
  linear_combination hω3
private lemma pMat_det : (graphFieldPermMat (F := F)).det = 1 := by
  simp [graphFieldPermMat, Matrix.det_fin_three]

private def graphFieldDiag (ω : F) (hω3 : ω ^ 3 = 1) : SL(3, F) :=
  ⟨graphFieldDiagMat ω, graphFieldDiagMat_det ω hω3⟩
private def graphFieldPerm : SL(3, F) := ⟨graphFieldPermMat, pMat_det⟩

private lemma d0_pow_three (ω : F) (hω3 : ω ^ 3 = 1) : (graphFieldDiag ω hω3) ^ 3 = 1 := by
  apply Subtype.ext
  show ((graphFieldDiag ω hω3 : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) ^ 3 = 1
  rw [show ((graphFieldDiag ω hω3 : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) =
      graphFieldDiagMat ω from rfl]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [graphFieldDiagMat, pow_succ, Matrix.mul_apply, Fin.sum_univ_three] <;> grind
private lemma p0_pow_three : (graphFieldPerm (F := F)) ^ 3 = 1 := by
  apply Subtype.ext
  show ((graphFieldPerm (F := F) : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) ^ 3 = 1
  rw [show ((graphFieldPerm (F := F) : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) =
      graphFieldPermMat from rfl]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [graphFieldPermMat, pow_succ, Matrix.mul_apply, Fin.sum_univ_three]

private def zHeis (ω : F) (hω0 : ω ≠ 0) (hω3 : ω ^ 3 = 1) : SL(3, F) :=
  LinearFlag.scalarElement (Units.mk0 ω hω0) (by
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, Units.val_mk0, hω3, Units.val_one])

private lemma zHeis_central (ω : F) (hω0 : ω ≠ 0) (hω3 : ω ^ 3 = 1) :
    ∀ g : SL(3, F), Commute g (zHeis ω hω0 hω3) := by
  intro g
  exact Subgroup.mem_center_iff.mp
    (LinearFlag.scalars_le_center 3 F (LinearFlag.scalarElement_mem_scalars _ _)) g

private lemma p0_conj_d0 (ω : F) (hω0 : ω ≠ 0) (hω3 : ω ^ 3 = 1) :
    graphFieldPerm⁻¹ * graphFieldDiag ω hω3 * graphFieldPerm =
      zHeis ω hω0 hω3 * graphFieldDiag ω hω3 := by
  have hp_inv : (graphFieldPerm (F := F))⁻¹ = graphFieldPerm * graphFieldPerm := by
    rw [← pow_two, (CFSG.Fischer.Classification.sq_eq_inv_of_pow_three p0_pow_three).symm]
  rw [hp_inv]
  apply Subtype.ext
  show (graphFieldPerm * graphFieldPerm * graphFieldDiag ω hω3 * graphFieldPerm).val =
    (zHeis ω hω0 hω3 * graphFieldDiag ω hω3).val
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
    Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [graphFieldDiag, graphFieldPerm, graphFieldDiagMat, graphFieldPermMat, zHeis,
      LinearFlag.coe_scalarElement, Units.val_mk0, pow_succ,
      Matrix.mul_apply, Fin.sum_univ_three] <;> grind

private lemma commutator_d0_p0 (ω : F) (hω0 : ω ≠ 0) (hω3 : ω ^ 3 = 1) :
    ⁅graphFieldDiag ω hω3, graphFieldPerm⁆ = zHeis ω hω0 hω3 := by
  have hconj := p0_conj_d0 ω hω0 hω3
  have hdp : graphFieldDiag ω hω3 * graphFieldPerm =
      zHeis ω hω0 hω3 * graphFieldPerm * graphFieldDiag ω hω3 := by
    calc graphFieldDiag ω hω3 * graphFieldPerm =
          graphFieldPerm * (graphFieldPerm⁻¹ * graphFieldDiag ω hω3 * graphFieldPerm) := by group
      _ = graphFieldPerm * (zHeis ω hω0 hω3 * graphFieldDiag ω hω3) := by rw [hconj]
      _ = zHeis ω hω0 hω3 * graphFieldPerm * graphFieldDiag ω hω3 := by
        rw [← (zHeis_central ω hω0 hω3 graphFieldPerm).eq]
        group
  rw [commutatorElement_def, hdp]
  group

private lemma d0_mul_p0_pow_three (ω : F) (hω3 : ω ^ 3 = 1) :
    (graphFieldDiag ω hω3 * graphFieldPerm) ^ 3 = 1 := by
  apply Subtype.ext
  show ((graphFieldDiag ω hω3 * graphFieldPerm) ^ 3).val = (1 : SL(3, F)).val
  rw [Matrix.SpecialLinearGroup.coe_pow, Matrix.SpecialLinearGroup.coe_mul]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [graphFieldDiag, graphFieldPerm, graphFieldDiagMat, graphFieldPermMat, pow_succ,
      Matrix.mul_apply, Fin.sum_univ_three] <;> grind

private lemma d0_mul_p0_inv_pow_three (ω : F) (hω3 : ω ^ 3 = 1) :
    (graphFieldDiag ω hω3 * graphFieldPerm⁻¹) ^ 3 = 1 := by
  have hp_inv : (graphFieldPerm (F := F))⁻¹ = graphFieldPerm * graphFieldPerm := by
    rw [← pow_two, (CFSG.Fischer.Classification.sq_eq_inv_of_pow_three p0_pow_three).symm]
  rw [hp_inv]
  apply Subtype.ext
  show ((graphFieldDiag ω hω3 * (graphFieldPerm * graphFieldPerm)) ^ 3).val = (1 : SL(3, F)).val
  rw [Matrix.SpecialLinearGroup.coe_pow, Matrix.SpecialLinearGroup.coe_mul,
    Matrix.SpecialLinearGroup.coe_mul]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [graphFieldDiag, graphFieldPerm, graphFieldDiagMat, graphFieldPermMat, pow_succ,
      Matrix.mul_apply, Fin.sum_univ_three] <;> grind

private lemma cubeRel_d0_p0 (ω : F) (hω3 : ω ^ 3 = 1) :
    CubeRel (graphFieldDiag ω hω3) graphFieldPerm :=
  ⟨d0_pow_three ω hω3, p0_pow_three, d0_mul_p0_pow_three ω hω3,
    d0_mul_p0_inv_pow_three ω hω3⟩

private lemma slGraphFieldAut_d0 (ω : F) (hω3 : ω ^ 3 = 1) :
    CFSG.ComponentClassification.CatalogueBGraphField.slGraphFieldAut 3 F graphFieldFrob
        (graphFieldDiag ω hω3) = graphFieldDiag ω hω3 := by
  have hd_inv : (graphFieldDiag ω hω3)⁻¹ = graphFieldDiag ω hω3 * graphFieldDiag ω hω3 := by
    rw [← pow_two, (sq_eq_inv_of_pow_three (d0_pow_three ω hω3)).symm]
  apply Matrix.SpecialLinearGroup.toGL_injective
  rw [CFSG.ComponentClassification.CatalogueBGraphField.toGL_slGraphFieldAut]
  apply Units.ext
  have hg : (Matrix.SpecialLinearGroup.toGL (graphFieldDiag ω hω3))⁻¹ =
      Matrix.SpecialLinearGroup.toGL (graphFieldDiag ω hω3 * graphFieldDiag ω hω3) := by
    rw [← map_inv, hd_inv]
  rw [CFSG.ComponentClassification.CatalogueBGraphField.glGraphFieldAut_matrix, hg,
    Matrix.SpecialLinearGroup.coe_GL_coe_matrix, Matrix.SpecialLinearGroup.coe_mul,
    Matrix.SpecialLinearGroup.coe_GL_coe_matrix]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [graphFieldDiag, graphFieldDiagMat, graphFieldFrob_apply, Matrix.transpose_apply,
      Matrix.mul_apply, Fin.sum_univ_three] <;> grind

private lemma slGraphFieldAut_p0 :
    CFSG.ComponentClassification.CatalogueBGraphField.slGraphFieldAut 3 F graphFieldFrob
        (graphFieldPerm (F := F)) = graphFieldPerm (F := F) := by
  have hp_inv : (graphFieldPerm (F := F))⁻¹ = graphFieldPerm * graphFieldPerm := by
    rw [← pow_two, (sq_eq_inv_of_pow_three p0_pow_three).symm]
  apply Matrix.SpecialLinearGroup.toGL_injective
  rw [CFSG.ComponentClassification.CatalogueBGraphField.toGL_slGraphFieldAut]
  apply Units.ext
  have hg : (Matrix.SpecialLinearGroup.toGL (graphFieldPerm (F := F)))⁻¹ =
      Matrix.SpecialLinearGroup.toGL (graphFieldPerm * graphFieldPerm) := by
    rw [← map_inv, hp_inv]
  rw [CFSG.ComponentClassification.CatalogueBGraphField.glGraphFieldAut_matrix, hg,
    Matrix.SpecialLinearGroup.coe_GL_coe_matrix, Matrix.SpecialLinearGroup.coe_mul,
    Matrix.SpecialLinearGroup.coe_GL_coe_matrix]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [graphFieldPerm, graphFieldPermMat, graphFieldFrob_apply, Matrix.transpose_apply,
      Matrix.mul_apply, Fin.sum_univ_three]

theorem repEquiv_one (ρ : Representation (ZMod 2) SL(3, F) U) :
    X7a.repEquiv ρ (1 : SL(3, F)) = 1 :=
  X7b.repLinEquiv_one ρ

theorem repEquiv_mul (ρ : Representation (ZMod 2) SL(3, F) U) (x y : SL(3, F)) :
    X7a.repEquiv ρ (x * y) = X7a.repEquiv ρ x * X7a.repEquiv ρ y :=
  X7b.repLinEquiv_mul ρ x y

theorem repEquiv_inv (ρ : Representation (ZMod 2) SL(3, F) U) (x : SL(3, F)) :
    X7a.repEquiv ρ x⁻¹ = (X7a.repEquiv ρ x)⁻¹ :=
  X7b.repLinEquiv_inv ρ x

theorem conj_repEquiv_of_intertwines (ρ : Representation (ZMod 2) SL(3, F) U)
    {a : U ≃ₗ[ZMod 2] U} (ha2 : a * a = 1) {x y : SL(3, F)}
    (h : X7a.Intertwines ρ a x y) :
    a * X7a.repEquiv ρ x * a = X7a.repEquiv ρ y := by
  refine LinearEquiv.ext fun u => ?_
  have h1 := h (a u)
  have h2 : a (a u) = u := by
    have := LinearEquiv.congr_fun ha2 u
    simpa using this
  show a (X7a.repEquiv ρ x (a u)) = X7a.repEquiv ρ y u
  change a (ρ x (a u)) = ρ y u
  rw [h1, h2]

private lemma zHeis_ne_one (ω : F) (hω0 : ω ≠ 0) (hω3 : ω ^ 3 = 1)
    (hω1 : ω ≠ 1) : zHeis ω hω0 hω3 ≠ 1 := by
  intro h
  have hmat : ((zHeis ω hω0 hω3 : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) 0 0 =
      ((1 : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) 0 0 := by rw [h]
  simp [zHeis, LinearFlag.coe_scalarElement, Units.val_mk0, Matrix.scalar_apply] at hmat
  exact hω1 hmat

theorem six_dvd_rank_of_graphField (hF : Fintype.card F = 2 ^ 2)
    (ρ : Representation (ZMod 2) SL(3, F) U)
    (hker : ∀ x : SL(3, F), ρ x = 1 → x ∈ LinearFlag.scalars 3 F)
    (hz : ∀ x ∈ LinearFlag.scalars 3 F, x ≠ 1 → ∀ u, ρ x u = u → u = 0)
    (a : U ≃ₗ[ZMod 2] U) (ha2 : a * a = 1) (A : GL (Fin 3) F) {j : ℕ} (hj : Odd j)
    (hb : ∀ x : SL(3, F), X7a.Intertwines ρ a x (X7Sec.graphFieldHom A j x)) :
    6 ∣ Module.finrank (ZMod 2) (LinearMap.range (a.toLinearMap - 1)) := by
  classical
  have hF4 : Nat.card F = 4 := by
    rw [Nat.card_eq_fintype_card, hF]
    norm_num
  let al : MulAut (SL(3, F)) := CFSG.QuasithinUnique.K1.stdAut A graphFieldFrob 1
  have hal : al = CFSG.QuasithinUnique.K1.stdAut A graphFieldFrob 1 := rfl
  have hstd : ∀ x : SL(3, F), X7Sec.graphFieldHom A j x = al x := by
    intro x
    have h := congrArg (fun f : SL(3, F) →* SL(3, F) => f x)
      (graphFieldHom_eq_stdAut hF hj A)
    simpa [al] using h
  have hα2 : ∀ x : SL(3, F), al (al x) = x :=
    mulAut_comp_self_eq_id ρ hker a ha2 A hb al hstd
  obtain ⟨H, hαβ⟩ := exists_conjugating_H hF A al hal hα2
  let G : MulAut (SL(3, F)) :=
    CFSG.ComponentClassification.CatalogueBGraphField.slGraphFieldAut 3 F graphFieldFrob
  let K : MulAut (SL(3, F)) :=
    CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation 3 F H
  obtain ⟨ω, hω0, hω1⟩ := LinearFieldFour.exists_ne_zero_ne_one hF4
  have hω3 : ω ^ 3 = 1 := LinearFieldFour.pow_three_eq_one hF4 hω0
  let z : SL(3, F) := zHeis ω hω0 hω3
  let d : SL(3, F) := K (graphFieldDiag ω hω3)
  let p : SL(3, F) := K graphFieldPerm
  have hKinv : K⁻¹ * K = 1 := inv_mul_cancel K
  have hfix_d : al d = d := by
    rw [show al = K * G * K⁻¹ from hαβ]
    change K (G (K⁻¹ (K (graphFieldDiag ω hω3)))) = K (graphFieldDiag ω hω3)
    rw [show K⁻¹ (K (graphFieldDiag ω hω3)) = graphFieldDiag ω hω3 from by
      simpa [MulAut.mul_apply] using
        congrArg (fun e : MulAut (SL(3, F)) => e (graphFieldDiag ω hω3)) hKinv]
    rw [slGraphFieldAut_d0]
  have hfix_p : al p = p := by
    rw [show al = K * G * K⁻¹ from hαβ]
    change K (G (K⁻¹ (K graphFieldPerm))) = K graphFieldPerm
    rw [show K⁻¹ (K graphFieldPerm) = graphFieldPerm from by
      simpa [MulAut.mul_apply] using congrArg (fun e : MulAut (SL(3, F)) => e graphFieldPerm) hKinv]
    rw [slGraphFieldAut_p0]
  have hfix_d' : X7Sec.graphFieldHom A j d = d := by rw [hstd d, hfix_d]
  have hfix_p' : X7Sec.graphFieldHom A j p = p := by rw [hstd p, hfix_p]
  have hR : CubeRel d p := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [show d = K (graphFieldDiag ω hω3) from rfl, ← map_pow, (cubeRel_d0_p0 ω hω3).cube_left,
        map_one]
    · rw [show p = K graphFieldPerm from rfl, ← map_pow, (cubeRel_d0_p0 ω hω3).cube_right, map_one]
    · rw [show d = K (graphFieldDiag ω hω3) from rfl, show p = K graphFieldPerm from rfl,
        ← map_mul, ← map_pow, (cubeRel_d0_p0 ω hω3).cube_mul, map_one]
    · rw [show d = K (graphFieldDiag ω hω3) from rfl, show p = K graphFieldPerm from rfl,
        ← map_inv, ← map_mul, ← map_pow, (cubeRel_d0_p0 ω hω3).cube_mul_inv, map_one]
  have hzmem : z ∈ LinearFlag.scalars 3 F :=
    LinearFlag.scalarElement_mem_scalars _ _
  have hz1 : z ≠ 1 := zHeis_ne_one ω hω0 hω3 hω1
  have hzc : ∀ g : SL(3, F), Commute g z := zHeis_central ω hω0 hω3
  have hcomm_dp : ⁅d, p⁆ = z := by
    have hω3u : (Units.mk0 ω hω0) ^ 3 = 1 := by
      apply Units.ext
      rw [Units.val_pow_eq_pow_val, Units.val_mk0, hω3, Units.val_one]
    have hzfix : K z = z :=
      CFSG.LocalAnalysis.RankThreeUC.S15.GN15.FFO.slConjugation_scalarElement
        (n := 3) H (Units.mk0 ω hω0) hω3u
    calc ⁅d, p⁆ = ⁅K (graphFieldDiag ω hω3), K graphFieldPerm⁆ := rfl
      _ = K ⁅graphFieldDiag ω hω3, graphFieldPerm⁆ := (map_commutatorElement K _ _).symm
      _ = K z := by rw [commutator_d0_p0 ω hω0 hω3]
      _ = z := hzfix
  have hcomm_d : a * X7a.repEquiv ρ d = X7a.repEquiv ρ d * a := by
    have h := conj_repEquiv_of_intertwines ρ ha2 (hb d)
    rw [hfix_d'] at h
    calc a * X7a.repEquiv ρ d = a * X7a.repEquiv ρ d * 1 := by rw [mul_one]
      _ = a * X7a.repEquiv ρ d * (a * a) := by rw [ha2]
      _ = (a * X7a.repEquiv ρ d * a) * a := by group
      _ = X7a.repEquiv ρ d * a := by rw [h]
  have hcomm_p : a * X7a.repEquiv ρ p = X7a.repEquiv ρ p * a := by
    have h := conj_repEquiv_of_intertwines ρ ha2 (hb p)
    rw [hfix_p'] at h
    calc a * X7a.repEquiv ρ p = a * X7a.repEquiv ρ p * 1 := by rw [mul_one]
      _ = a * X7a.repEquiv ρ p * (a * a) := by rw [ha2]
      _ = (a * X7a.repEquiv ρ p * a) * a := by group
      _ = X7a.repEquiv ρ p * a := by rw [h]
  let T : Subgroup (SL(3, F)) :=
    { carrier := {x | a * X7a.repEquiv ρ x = X7a.repEquiv ρ x * a}
      one_mem' := by simp [repEquiv_one]
      mul_mem' := by
        intro x y hx hy
        change a * X7a.repEquiv ρ (x * y) = X7a.repEquiv ρ (x * y) * a
        rw [repEquiv_mul]
        calc a * (X7a.repEquiv ρ x * X7a.repEquiv ρ y) =
              (a * X7a.repEquiv ρ x) * X7a.repEquiv ρ y := by group
          _ = (X7a.repEquiv ρ x * a) * X7a.repEquiv ρ y := by rw [hx]
          _ = X7a.repEquiv ρ x * (a * X7a.repEquiv ρ y) := by group
          _ = X7a.repEquiv ρ x * (X7a.repEquiv ρ y * a) := by rw [hy]
          _ = (X7a.repEquiv ρ x * X7a.repEquiv ρ y) * a := by group
      inv_mem' := by
        intro x hx
        change a * X7a.repEquiv ρ x⁻¹ = X7a.repEquiv ρ x⁻¹ * a
        rw [repEquiv_inv]
        calc a * (X7a.repEquiv ρ x)⁻¹ =
              (X7a.repEquiv ρ x)⁻¹ * (X7a.repEquiv ρ x * a) *
                (X7a.repEquiv ρ x)⁻¹ := by group
          _ = (X7a.repEquiv ρ x)⁻¹ * (a * X7a.repEquiv ρ x) *
                (X7a.repEquiv ρ x)⁻¹ := by rw [← hx]
          _ = (X7a.repEquiv ρ x)⁻¹ * a := by group }
  let Q : Subgroup (SL(3, F)) := Subgroup.closure ({d, p} : Set (SL(3, F)))
  have hQT : Q ≤ T := by
    rw [Subgroup.closure_le]
    intro x hx
    rcases hx with rfl | rfl
    · exact hcomm_d
    · exact hcomm_p
  let R : Submodule (ZMod 2) U := LinearMap.range (a.toLinearMap - 1)
  have hRinv : ∀ q : Q, ∀ w ∈ R, ρ (q : SL(3, F)) w ∈ R := by
    intro q w hw
    obtain ⟨u, rfl⟩ := hw
    have hcomm : a * X7a.repEquiv ρ (q : SL(3, F)) = X7a.repEquiv ρ (q : SL(3, F)) * a :=
      hQT q.2
    have h1 : a (ρ (q : SL(3, F)) u) = ρ (q : SL(3, F)) (a u) := by
      have := congrArg (fun e : U ≃ₗ[ZMod 2] U => e u) hcomm
      simpa [X7a.repEquiv, LinearEquiv.mul_apply] using this
    refine ⟨ρ (q : SL(3, F)) u, ?_⟩
    simp only [LinearMap.sub_apply, Module.End.one_apply, map_sub]
    exact congrArg (fun x : U => x - ρ (q : SL(3, F)) u) h1
  let S : Subrepresentation (ρ.comp Q.subtype) :=
    { toSubmodule := R
      apply_mem_toSubmodule := fun q w hw => hRinv q w hw }
  let ρR : Representation (ZMod 2) Q R := S.toRepresentation
  let xQ : Q := ⟨d, Subgroup.subset_closure (by simp)⟩
  let yQ : Q := ⟨p, Subgroup.subset_closure (by simp)⟩
  have hzQ : ((⁅xQ, yQ⁆ : Q) : SL(3, F)) = z := by
    change Q.subtype ⁅xQ, yQ⁆ = z
    rw [map_commutatorElement Q.subtype xQ yQ]
    exact hcomm_dp
  have hzcentralQ : ∀ g : Q, Commute g ⁅xQ, yQ⁆ := by
    intro g
    apply Subtype.ext
    change (g : SL(3, F)) * ((⁅xQ, yQ⁆ : Q) : SL(3, F)) =
      ((⁅xQ, yQ⁆ : Q) : SL(3, F)) * (g : SL(3, F))
    rw [hzQ]
    exact hzc (g : SL(3, F))
  have hexpQ : ∀ g : Q, g ^ 3 = 1 := by
    intro g
    apply Subtype.ext
    rw [Subgroup.coe_pow]
    exact hR.pow_three_eq_one g.2
  have h6 := CFSG.Quasithin.VolI.six_dvd_finrank_centralImage
    (ρ := ρR) (x := xQ) (y := yQ) hzcentralQ hexpQ
  have hcentralImage : CFSG.LinearAlgebra.centralImage ρR ⁅xQ, yQ⁆ = ⊤ := by
    rw [CFSG.LinearAlgebra.centralImage, LinearMap.range_eq_top]
    apply Finite.injective_iff_surjective.mp
    intro w1 w2 hw
    have h'' : (ρR ⁅xQ, yQ⁆ - 1) (w1 - w2) = 0 := by
      rw [map_sub]
      exact sub_eq_zero.mpr hw
    rw [LinearMap.sub_apply, Module.End.one_apply] at h''
    have hfix : ρR ⁅xQ, yQ⁆ (w1 - w2) = w1 - w2 := sub_eq_zero.mp h''
    have hzapp : ρ (z) (((w1 - w2 : R)) : U) = (((w1 - w2 : R)) : U) := by
      have := congrArg Subtype.val hfix
      simpa [ρR, S, Subrepresentation.toRepresentation, hzQ] using this
    have hzero : (((w1 - w2 : R)) : U) = 0 := hz z hzmem hz1 _ hzapp
    have hU : ((w1 : R) : U) = ((w2 : R) : U) := by
      have h' : ((w1 : R) : U) - ((w2 : R) : U) = 0 := by
        simpa using hzero
      exact sub_eq_zero.mp h'
    exact Subtype.ext hU
  rw [hcentralImage] at h6
  simpa using h6
end Rep

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Thm14_2
