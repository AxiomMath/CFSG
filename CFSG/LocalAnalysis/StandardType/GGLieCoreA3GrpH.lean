module

public import CFSG.LocalAnalysis.StandardType.GGLieCoreA3LatticeE6Defs
public import CFSG.LocalAnalysis.StandardType.GGLieCoreA3GrpWeyl
public import CFSG.LocalAnalysis.StandardType.GGLieCoreA3DictPhi
public import CFSG.HardMathSupport.Timmesfeld.Torality.LangAssembly
public import CFSG.LieType.Chevalley.LangStronglyOrthogonalCommute
public import CFSG.LieType.Chevalley.E6GraphInvertedRootRotation
public import CFSG.LieType.Chevalley.GraphFixedHighestRoot
public import CFSG.LieType.Chevalley.OrthogonalFixedOrbitMaps
public import CFSG.RankThree.Chevalley.SteinbergCEF4EvenQPlusWeyl
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.BigAnyTorus
public import CFSG.LieType.AlgebraicGroups.ToralTwistPinningFrobenius
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.BigAnyDefs
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.CentralizerTrivialPoly
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.RigidField
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.RigidNorm
public import CFSG.HardMathSupport.Timmesfeld.LocalTwo.LangFrame

public section

namespace CFSG.StandardType.LieCore

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Universal
  CFSG.StandardType CFSG.StandardType.GGFinModel CFSG.LieType.Chevalley
  CFSG.LieType.AlgebraicGroups CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.RankThree.PartOne.KE
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Timmesfeld.Torality
open CFSG.Open (StatedLieTag)
open CFSG.LieType.Steinberg.Adjoint (iform)
open CFSG.RankThree.Chevalley.EvenF4QPlus
open Matrix

private noncomputable def ggLieGH_zeta : GGLˣ := ggZeta 3 Nat.prime_three (by norm_num)
private theorem ggLieGH_zeta_order : orderOf ggLieGH_zeta = 3 := by
  unfold ggLieGH_zeta ggZeta
  exact (exists_zeta GGL Nat.prime_three (by norm_num)).choose_spec

private theorem ggLieGH_zeta_pow_three : ggLieGH_zeta ^ 3 = 1 := by
  rw [← ggLieGH_zeta_order]
  exact pow_orderOf_eq_one _

private theorem ggLieGH_zeta_ne_one : ggLieGH_zeta ≠ 1 := by
  intro h
  have h1 := ggLieGH_zeta_order
  rw [h, orderOf_one] at h1
  omega

private theorem ggLieGH_char_two : (2 : GGL) = 0 := by
  haveI : CharP GGL 2 := inferInstance
  exact_mod_cast CharP.cast_eq_zero GGL 2

private theorem ggLieGH_neg_eq_self (z : GGL) : -z = z := by
  have h : z + z = 0 := by rw [← two_mul, ggLieGH_char_two, zero_mul]
  rw [neg_eq_iff_add_eq_zero]
  exact h

private theorem ggLieGH_neg_one : -(1 : GGL) = 1 := ggLieGH_neg_eq_self 1
private theorem ggLieGH_one_add_one : (1 : GGL) + 1 = 0 := by
  rw [← two_mul, ggLieGH_char_two, zero_mul]

private theorem ggLieGH_zeta_coe_pow_three : (ggLieGH_zeta : GGL) ^ 3 = 1 := by
  have := congrArg Units.val ggLieGH_zeta_pow_three
  simpa using this

private theorem ggLieGH_zeta_sq_add : (ggLieGH_zeta : GGL) ^ 2 + (ggLieGH_zeta : GGL) = 1 := by
  have hz3 : (ggLieGH_zeta : GGL) ^ 3 = 1 := ggLieGH_zeta_coe_pow_three
  have hz1 : (ggLieGH_zeta : GGL) ≠ 1 := fun h => ggLieGH_zeta_ne_one (Units.ext h)
  have h0 : ((ggLieGH_zeta : GGL) - 1) *
      ((ggLieGH_zeta : GGL) ^ 2 + (ggLieGH_zeta : GGL) + 1) = 0 := by
    linear_combination hz3
  have h1 : (ggLieGH_zeta : GGL) ^ 2 + (ggLieGH_zeta : GGL) + 1 = 0 := by
    rcases mul_eq_zero.1 h0 with h | h
    · exact absurd (sub_eq_zero.1 h) hz1
    · exact h
  have hneg : -(1 : GGL) = 1 := ggLieGH_neg_one
  linear_combination h1 + hneg

private theorem ggLieGH_zeta_sq : (ggLieGH_zeta : GGL) ^ 2 = 1 + (ggLieGH_zeta : GGL) := by
  have h := (eq_sub_iff_add_eq.2 ggLieGH_zeta_sq_add :
    (ggLieGH_zeta : GGL) ^ 2 = 1 - (ggLieGH_zeta : GGL))
  rwa [sub_eq_add_neg, ggLieGH_neg_eq_self] at h

private theorem ggLieGH_zeta_eq : (ggLieGH_zeta : GGL) = 1 + (ggLieGH_zeta : GGL) ^ 2 := by
  rw [ggLieGH_zeta_sq]
  rw [show (1 : GGL) + (1 + (ggLieGH_zeta : GGL)) = (1 + 1) + (ggLieGH_zeta : GGL) by abel,
    ggLieGH_one_add_one, zero_add]

private theorem ggLieGH_zeta_pow_four : (ggLieGH_zeta : GGL) ^ 4 = (ggLieGH_zeta : GGL) := by
  rw [show (4 : ℕ) = 3 + 1 by norm_num, pow_succ, ggLieGH_zeta_coe_pow_three, one_mul]

private theorem ggLieGH_zeta_sq_sq : ((ggLieGH_zeta : GGL) ^ 2) ^ 2 = (ggLieGH_zeta : GGL) := by
  rw [← pow_mul]
  norm_num
  rw [ggLieGH_zeta_pow_four]

private theorem ggLieGH_zeta_inv :
    ((ggLieGH_zeta⁻¹ : GGLˣ) : GGL) = (ggLieGH_zeta : GGL) ^ 2 := by
  have hmul : ggLieGH_zeta * ggLieGH_zeta ^ 2 = 1 := by
    rw [← pow_succ' ggLieGH_zeta 2]
    norm_num
    exact ggLieGH_zeta_pow_three
  have hinv : ggLieGH_zeta⁻¹ = ggLieGH_zeta ^ 2 := inv_eq_of_mul_eq_one_right hmul
  rw [hinv, Units.val_pow_eq_pow_val]

private theorem ggLieGH_zeta_inv' : (ggLieGH_zeta : GGL)⁻¹ = (ggLieGH_zeta : GGL) ^ 2 := by
  rw [← Units.val_inv_eq_inv_val, ggLieGH_zeta_inv]

private noncomputable def ggLieGH_h2 : SL2 GGL :=
  ⟨!![1, 1; (ggLieGH_zeta : GGL), (ggLieGH_zeta : GGL) ^ 2], by
    rw [Matrix.det_fin_two_of]
    simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_fin_one, Matrix.empty_val', one_mul]
    rw [sub_eq_add_neg, ggLieGH_neg_eq_self]
    exact ggLieGH_zeta_sq_add⟩

private theorem ggLieGH_h2_coe :
    ((ggLieGH_h2 : SL2 GGL) : Matrix (Fin 2) (Fin 2) GGL) =
      !![1, 1; (ggLieGH_zeta : GGL), (ggLieGH_zeta : GGL) ^ 2] := rfl
private theorem ggLieGH_nSL_one_coe :
    ((nSL (1 : GGLˣ) : SL2 GGL) : Matrix (Fin 2) (Fin 2) GGL) = !![0, 1; 1, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [nSL, ggLieGH_neg_one]

private theorem ggLieGH_h2_frob :
    Matrix.SpecialLinearGroup.map (iterateFrobenius GGL 2 1) ggLieGH_h2 =
      ggLieGH_h2 * nSL (1 : GGLˣ) := by
  apply Subtype.ext
  show ((ggLieGH_h2 : SL2 GGL) : Matrix (Fin 2) (Fin 2) GGL).map (iterateFrobenius GGL 2 1) =
    ((ggLieGH_h2 * nSL (1 : GGLˣ) : SL2 GGL) : Matrix (Fin 2) (Fin 2) GGL)
  rw [Matrix.SpecialLinearGroup.coe_mul, ggLieGH_h2_coe, ggLieGH_nSL_one_coe]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.map_apply, Matrix.mul_apply, Fin.sum_univ_two, iterateFrobenius_def,
      frobenius_def, ggLieGH_zeta_coe_pow_three, ggLieGH_zeta_sq_sq]

private theorem ggLieGH_h2_conj_diag :
    ggLieGH_h2 * HSL ggLieGH_zeta * ggLieGH_h2⁻¹ = uSL 1 * vSL 1 := by
  rw [mul_inv_eq_iff_eq_mul]
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
    Matrix.SpecialLinearGroup.coe_mul, ggLieGH_h2_coe, coe_HSL, coe_uSL, coe_vSL]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, ggLieGH_zeta_inv', ggLieGH_neg_eq_self,
      ggLieGH_neg_one, ggLieGH_one_add_one]
  · rw [← pow_two]; exact ggLieGH_zeta_sq
  · rw [← pow_two, ggLieGH_zeta_sq_sq]
    exact ggLieGH_zeta_eq

private theorem ggLieGH_not_isRoot_add
    {α β : Fin (langTag .E6).rank → ℤ} (hα : IsRoot (langTag .E6) α)
    (hβ : IsRoot (langTag .E6) β) (h0 : iform α β = 0) :
    ¬ IsRoot (langTag .E6) (α + β) := by
  intro h
  have h4 : iform (α + β) (α + β) = 4 := by
    have hα2 : iform α α = 2 := iform_self_eq_two (Or.inr (Or.inl rfl)) hα
    have hβ2 : iform β β = 2 := iform_self_eq_two (Or.inr (Or.inl rfl)) hβ
    rw [CFSG.LieType.Steinberg.Adjoint.iform_add_left,
      CFSG.LieType.Steinberg.Adjoint.iform_add_right,
      CFSG.LieType.Steinberg.Adjoint.iform_add_right,
      CFSG.LieType.Steinberg.Adjoint.iform_comm β α, h0, hα2, hβ2]
    norm_num
  have h2 := iform_self_eq_two (Or.inr (Or.inl rfl)) h
  exact absurd (h4.symm.trans h2) (by norm_num)

private theorem ggLieGH_not_isRoot_sub
    {α β : Fin (langTag .E6).rank → ℤ} (hα : IsRoot (langTag .E6) α)
    (hβ : IsRoot (langTag .E6) β) (h0 : iform α β = 0) :
    ¬ IsRoot (langTag .E6) (α - β) := by
  intro h
  have h4 : iform (α - β) (α - β) = 4 := by
    have hα2 : iform α α = 2 := iform_self_eq_two (Or.inr (Or.inl rfl)) hα
    have hβ2 : iform β β = 2 := iform_self_eq_two (Or.inr (Or.inl rfl)) hβ
    rw [CFSG.LieType.Steinberg.Adjoint.iform_sub_left,
      CFSG.LieType.Steinberg.Adjoint.iform_sub_right,
      CFSG.LieType.Steinberg.Adjoint.iform_sub_right,
      CFSG.LieType.Steinberg.Adjoint.iform_comm β α, h0, hα2, hβ2]
    norm_num
  have h2 := iform_self_eq_two (Or.inr (Or.inl rfl)) h
  exact absurd (h4.symm.trans h2) (by norm_num)

private theorem ggLieGH_rootSL2_uSL
    {β : Fin (langTag .E6).rank → ℤ} (z : GGL) :
    rootSL2 (langTag .E6) GGL β (uSL z) = pinnedX (langTag .E6) GGL β z := by
  rw [rootSL2_uSL_eq]
  congr 1
  rcases pinnedSign_eq (langTag .E6) β with h | h
  · rw [h]; simp
  · rw [h, neg_one_smul, ggLieGH_neg_eq_self]

private theorem ggLieGH_rootSL2_vSL
    {β : Fin (langTag .E6).rank → ℤ}
    (hβ : IsRoot (langTag .E6) β) (z : GGL) :
    rootSL2 (langTag .E6) GGL β (vSL z) = pinnedX (langTag .E6) GGL (-β) z := by
  obtain ⟨ε, hε, h⟩ := exists_rootSL2_vSL_eq (K := GGL) hβ
  rw [h z]
  have hε1 : ε = 1 := eq_one_of_mul_self_eq_one_of_two_eq_zero ggLieGH_char_two hε
  rw [hε1, one_mul]

private theorem ggLieGH_commute_rootSL2
    {α β : Fin (langTag .E6).rank → ℤ} (hα : IsRoot (langTag .E6) α)
    (hβ : IsRoot (langTag .E6) β) (h0 : iform α β = 0) (A B : SL2 GGL) :
    rootSL2 (langTag .E6) GGL α A * rootSL2 (langTag .E6) GGL β B =
      rootSL2 (langTag .E6) GGL β B * rootSL2 (langTag .E6) GGL α A :=
  exceptional_Lang_strongly_orthogonal_root_rank_one_commutation (langTag .E6) GGL hα hβ h0
    (ggLieGH_not_isRoot_add hα hβ h0) (ggLieGH_not_isRoot_sub hα hβ h0)
    _ ⟨A, rfl⟩ _ ⟨B, rfl⟩

private theorem ggLieGH_ggPhi_rootSL2
    {β : Fin (langTag .E6).rank → ℤ} (hβ : IsRoot (langTag .E6) β) (A : SL2 GGL) :
    ggPhi .E6 1 (rootSL2 (langTag .E6) GGL β A) =
      rootSL2 (langTag .E6) GGL β (Matrix.SpecialLinearGroup.map (iterateFrobenius GGL 2 1) A) := by
  have hΦ : ggPhi .E6 1 = entrywiseFrobGL (langTag .E6) GGL (p := 2) 1 := rfl
  rw [hΦ]
  exact entrywiseFrobGL_rootSL2 2 1 hβ A

private theorem ggLieGH_rootDiag_eq_HSL
    {β : Fin (langTag .E6).rank → ℤ} (hβ : IsRoot (langTag .E6) β) :
    rootDiagUnit (langTag .E6) (ggLieCorootUnit β) =
      rootSL2 (langTag .E6) GGL β (HSL ggLieGH_zeta) := by
  rw [← Hel_root_eq_rootSL2 (τ := langTag .E6) (L := GGL) (Or.inr (Or.inl rfl)) hβ
    ggLieGH_zeta]
  congr 1
  funext j
  simp [ggLieCorootUnit, Hchar, ggLieGH_zeta, CFSG.LieType.Steinberg.Adjoint.iform_comm]

private theorem ggLieGH_commute_pinnedX_rootSL2
    {ψ β : Fin (langTag .E6).rank → ℤ} (hψ : IsRoot (langTag .E6) ψ)
    (hβ : IsRoot (langTag .E6) β) (h0 : iform ψ β = 0) (t : GGL) :
    pinnedX (langTag .E6) GGL ψ t * rootSL2 (langTag .E6) GGL β ggLieGH_h2 =
      rootSL2 (langTag .E6) GGL β ggLieGH_h2 * pinnedX (langTag .E6) GGL ψ t :=
  exceptional_Lang_strongly_orthogonal_root_rank_one_commutation (langTag .E6) GGL hψ hβ h0
    (ggLieGH_not_isRoot_add hψ hβ h0) (ggLieGH_not_isRoot_sub hψ hβ h0)
    _ ⟨uSL t, ggLieGH_rootSL2_uSL t⟩ _ ⟨ggLieGH_h2, rfl⟩

theorem ggLie_exists_h
    {β₀ β₁ : Fin (langTag .E6).rank → ℤ} (h₀ : IsRoot (langTag .E6) β₀)
    (h₁ : IsRoot (langTag .E6) β₁) (horth : iform β₀ β₁ = 0) :
    ∃ h ∈ adjointGroup (langTag .E6) GGL,
      ggPhi .E6 1 h = h * canonicalRep (coxeterSystem (langTag .E6)) GGL
        (rootReflection β₀ * rootReflection β₁) ∧
      h * rootDiagUnit (langTag .E6) (ggLieCorootUnit β₀) * h⁻¹ =
        pinnedX (langTag .E6) GGL β₀ 1 * pinnedX (langTag .E6) GGL (-β₀) 1 ∧
      h * rootDiagUnit (langTag .E6) (ggLieCorootUnit β₁) * h⁻¹ =
        pinnedX (langTag .E6) GGL β₁ 1 * pinnedX (langTag .E6) GGL (-β₁) 1 ∧
      ∀ ψ, IsRoot (langTag .E6) ψ → iform ψ β₀ = 0 → iform ψ β₁ = 0 → ∀ t : GGL,
        h * pinnedX (langTag .E6) GGL ψ t * h⁻¹ = pinnedX (langTag .E6) GGL ψ t := by
  have horth' : iform β₁ β₀ = 0 := by rw [CFSG.LieType.Steinberg.Adjoint.iform_comm]; exact horth
  refine ⟨rootSL2 (langTag .E6) GGL β₀ ggLieGH_h2 * rootSL2 (langTag .E6) GGL β₁ ggLieGH_h2,
    mul_mem (rootSL2_mem_adjointGroup β₀ ggLieGH_h2)
      (rootSL2_mem_adjointGroup β₁ ggLieGH_h2), ?_, ?_, ?_, ?_⟩
  · have hΦ0 : ggPhi .E6 1 (rootSL2 (langTag .E6) GGL β₀ ggLieGH_h2) =
        rootSL2 (langTag .E6) GGL β₀ (ggLieGH_h2 * nSL 1) := by
      rw [ggLieGH_ggPhi_rootSL2 h₀, ggLieGH_h2_frob]
    have hΦ1 : ggPhi .E6 1 (rootSL2 (langTag .E6) GGL β₁ ggLieGH_h2) =
        rootSL2 (langTag .E6) GGL β₁ (ggLieGH_h2 * nSL 1) := by
      rw [ggLieGH_ggPhi_rootSL2 h₁, ggLieGH_h2_frob]
    have hn0 : rootSL2 (langTag .E6) GGL β₀ (nSL 1) =
        canonicalRep (coxeterSystem (langTag .E6)) GGL (rootReflection β₀) :=
      rootWeylSL2_one_eq_canonicalRep_of_charTwo h₀
    have hn1 : rootSL2 (langTag .E6) GGL β₁ (nSL 1) =
        canonicalRep (coxeterSystem (langTag .E6)) GGL (rootReflection β₁) :=
      rootWeylSL2_one_eq_canonicalRep_of_charTwo h₁
    have hc : rootSL2 (langTag .E6) GGL β₀ (nSL 1) * rootSL2 (langTag .E6) GGL β₁ ggLieGH_h2 =
        rootSL2 (langTag .E6) GGL β₁ ggLieGH_h2 *
          rootSL2 (langTag .E6) GGL β₀ (nSL 1) :=
      ggLieGH_commute_rootSL2 h₀ h₁ horth (nSL 1) ggLieGH_h2
    rw [map_mul, hΦ0, hΦ1, map_mul, map_mul]
    calc (rootSL2 (langTag .E6) GGL β₀ ggLieGH_h2 * rootSL2 (langTag .E6) GGL β₀ (nSL 1)) *
            (rootSL2 (langTag .E6) GGL β₁ ggLieGH_h2 * rootSL2 (langTag .E6) GGL β₁ (nSL 1))
        = rootSL2 (langTag .E6) GGL β₀ ggLieGH_h2 *
            (rootSL2 (langTag .E6) GGL β₀ (nSL 1) * rootSL2 (langTag .E6) GGL β₁ ggLieGH_h2) *
            rootSL2 (langTag .E6) GGL β₁ (nSL 1) := by group
      _ = rootSL2 (langTag .E6) GGL β₀ ggLieGH_h2 *
            (rootSL2 (langTag .E6) GGL β₁ ggLieGH_h2 * rootSL2 (langTag .E6) GGL β₀ (nSL 1)) *
            rootSL2 (langTag .E6) GGL β₁ (nSL 1) := by rw [hc]
      _ = (rootSL2 (langTag .E6) GGL β₀ ggLieGH_h2 * rootSL2 (langTag .E6) GGL β₁ ggLieGH_h2) *
            (rootSL2 (langTag .E6) GGL β₀ (nSL 1) * rootSL2 (langTag .E6) GGL β₁ (nSL 1)) := by
            group
      _ = (rootSL2 (langTag .E6) GGL β₀ ggLieGH_h2 * rootSL2 (langTag .E6) GGL β₁ ggLieGH_h2) *
            canonicalRep (coxeterSystem (langTag .E6)) GGL
              (rootReflection β₀ * rootReflection β₁) := by
            rw [hn0, hn1, ggLie_canonicalRep_mul (rootReflection β₀) (rootReflection β₁)]
  · have hd : rootDiagUnit (langTag .E6) (ggLieCorootUnit β₀) =
        rootSL2 (langTag .E6) GGL β₀ (HSL ggLieGH_zeta) := ggLieGH_rootDiag_eq_HSL h₀
    rw [hd]
    have hc : rootSL2 (langTag .E6) GGL β₁ ggLieGH_h2 *
        rootSL2 (langTag .E6) GGL β₀ (HSL ggLieGH_zeta) =
        rootSL2 (langTag .E6) GGL β₀ (HSL ggLieGH_zeta) *
          rootSL2 (langTag .E6) GGL β₁ ggLieGH_h2 :=
      (ggLieGH_commute_rootSL2 h₀ h₁ horth (HSL ggLieGH_zeta) ggLieGH_h2).symm
    calc (rootSL2 (langTag .E6) GGL β₀ ggLieGH_h2 *
            rootSL2 (langTag .E6) GGL β₁ ggLieGH_h2) *
          rootSL2 (langTag .E6) GGL β₀ (HSL ggLieGH_zeta) *
          (rootSL2 (langTag .E6) GGL β₀ ggLieGH_h2 *
            rootSL2 (langTag .E6) GGL β₁ ggLieGH_h2)⁻¹
        = rootSL2 (langTag .E6) GGL β₀ ggLieGH_h2 *
            (rootSL2 (langTag .E6) GGL β₁ ggLieGH_h2 *
              rootSL2 (langTag .E6) GGL β₀ (HSL ggLieGH_zeta)) *
            (rootSL2 (langTag .E6) GGL β₁ ggLieGH_h2)⁻¹ *
            (rootSL2 (langTag .E6) GGL β₀ ggLieGH_h2)⁻¹ := by group
      _ = rootSL2 (langTag .E6) GGL β₀ ggLieGH_h2 *
            (rootSL2 (langTag .E6) GGL β₀ (HSL ggLieGH_zeta) *
              rootSL2 (langTag .E6) GGL β₁ ggLieGH_h2) *
            (rootSL2 (langTag .E6) GGL β₁ ggLieGH_h2)⁻¹ *
            (rootSL2 (langTag .E6) GGL β₀ ggLieGH_h2)⁻¹ := by rw [hc]
      _ = rootSL2 (langTag .E6) GGL β₀ ggLieGH_h2 *
            rootSL2 (langTag .E6) GGL β₀ (HSL ggLieGH_zeta) *
            (rootSL2 (langTag .E6) GGL β₀ ggLieGH_h2)⁻¹ := by group
      _ = rootSL2 (langTag .E6) GGL β₀
            (ggLieGH_h2 * HSL ggLieGH_zeta * ggLieGH_h2⁻¹) := by
            rw [map_mul, map_mul, map_inv]
      _ = rootSL2 (langTag .E6) GGL β₀ (uSL 1 * vSL 1) := by rw [ggLieGH_h2_conj_diag]
      _ = pinnedX (langTag .E6) GGL β₀ 1 * pinnedX (langTag .E6) GGL (-β₀) 1 := by
            rw [map_mul, ggLieGH_rootSL2_uSL, ggLieGH_rootSL2_vSL h₀]
  · have hd : rootDiagUnit (langTag .E6) (ggLieCorootUnit β₁) =
        rootSL2 (langTag .E6) GGL β₁ (HSL ggLieGH_zeta) := ggLieGH_rootDiag_eq_HSL h₁
    rw [hd]
    have hc : rootSL2 (langTag .E6) GGL β₀ ggLieGH_h2 *
        rootSL2 (langTag .E6) GGL β₁ (uSL 1 * vSL 1) =
        rootSL2 (langTag .E6) GGL β₁ (uSL 1 * vSL 1) *
          rootSL2 (langTag .E6) GGL β₀ ggLieGH_h2 :=
      ggLieGH_commute_rootSL2 h₀ h₁ horth ggLieGH_h2 (uSL 1 * vSL 1)
    calc (rootSL2 (langTag .E6) GGL β₀ ggLieGH_h2 *
            rootSL2 (langTag .E6) GGL β₁ ggLieGH_h2) *
          rootSL2 (langTag .E6) GGL β₁ (HSL ggLieGH_zeta) *
          (rootSL2 (langTag .E6) GGL β₀ ggLieGH_h2 *
            rootSL2 (langTag .E6) GGL β₁ ggLieGH_h2)⁻¹
        = rootSL2 (langTag .E6) GGL β₀ ggLieGH_h2 *
            (rootSL2 (langTag .E6) GGL β₁ ggLieGH_h2 *
              rootSL2 (langTag .E6) GGL β₁ (HSL ggLieGH_zeta) *
              (rootSL2 (langTag .E6) GGL β₁ ggLieGH_h2)⁻¹) *
            (rootSL2 (langTag .E6) GGL β₀ ggLieGH_h2)⁻¹ := by group
      _ = rootSL2 (langTag .E6) GGL β₀ ggLieGH_h2 *
            rootSL2 (langTag .E6) GGL β₁
              (ggLieGH_h2 * HSL ggLieGH_zeta * ggLieGH_h2⁻¹) *
            (rootSL2 (langTag .E6) GGL β₀ ggLieGH_h2)⁻¹ := by
            rw [map_mul, map_mul, map_inv]
      _ = rootSL2 (langTag .E6) GGL β₀ ggLieGH_h2 *
            rootSL2 (langTag .E6) GGL β₁ (uSL 1 * vSL 1) *
            (rootSL2 (langTag .E6) GGL β₀ ggLieGH_h2)⁻¹ := by
            rw [ggLieGH_h2_conj_diag]
      _ = rootSL2 (langTag .E6) GGL β₁ (uSL 1 * vSL 1) := by rw [hc]; group
      _ = pinnedX (langTag .E6) GGL β₁ 1 * pinnedX (langTag .E6) GGL (-β₁) 1 := by
            rw [map_mul, ggLieGH_rootSL2_uSL, ggLieGH_rootSL2_vSL h₁]
  · intro ψ hψ hψ0 hψ1 t
    have hc0 := ggLieGH_commute_pinnedX_rootSL2 hψ h₀ hψ0 t
    have hc1 := ggLieGH_commute_pinnedX_rootSL2 hψ h₁ hψ1 t
    calc (rootSL2 (langTag .E6) GGL β₀ ggLieGH_h2 *
            rootSL2 (langTag .E6) GGL β₁ ggLieGH_h2) * pinnedX (langTag .E6) GGL ψ t *
          (rootSL2 (langTag .E6) GGL β₀ ggLieGH_h2 *
            rootSL2 (langTag .E6) GGL β₁ ggLieGH_h2)⁻¹
        = rootSL2 (langTag .E6) GGL β₀ ggLieGH_h2 *
            (rootSL2 (langTag .E6) GGL β₁ ggLieGH_h2 * pinnedX (langTag .E6) GGL ψ t) *
            (rootSL2 (langTag .E6) GGL β₁ ggLieGH_h2)⁻¹ *
            (rootSL2 (langTag .E6) GGL β₀ ggLieGH_h2)⁻¹ := by group
      _ = rootSL2 (langTag .E6) GGL β₀ ggLieGH_h2 *
            (pinnedX (langTag .E6) GGL ψ t * rootSL2 (langTag .E6) GGL β₁ ggLieGH_h2) *
            (rootSL2 (langTag .E6) GGL β₁ ggLieGH_h2)⁻¹ *
            (rootSL2 (langTag .E6) GGL β₀ ggLieGH_h2)⁻¹ := by rw [hc1]
      _ = rootSL2 (langTag .E6) GGL β₀ ggLieGH_h2 * pinnedX (langTag .E6) GGL ψ t *
            (rootSL2 (langTag .E6) GGL β₀ ggLieGH_h2)⁻¹ := by group
      _ = pinnedX (langTag .E6) GGL ψ t := by rw [← hc0]; group

end CFSG.StandardType.LieCore
