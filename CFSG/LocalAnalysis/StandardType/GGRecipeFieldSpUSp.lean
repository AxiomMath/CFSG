module

public import CFSG.LocalAnalysis.StandardType.GGRecipeFieldSpUNorm
public import CFSG.LocalAnalysis.ComponentInitial.SymplecticHigherOuterQuotient
import CFSG.RankThree.PartTwo.KFacts.AutPSpOrderThree
import CFSG.RankThree.Classical.SemilinearFixedBasis
import TauCeti.LinearAlgebra.BilinearForm.SymplecticBasis
public import CFSG.CharacterTheory.Semidihedral.DihedralQuaternion
public import CFSG.LocalAnalysis.ComponentInitial.SymplecticFlagOrder
public import CFSG.LocalAnalysis.ComponentInitial.SymplecticHigherBruhat
public import CFSG.Open.Defs
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PCore.PCore
import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore

public section

namespace CFSG.StandardType

namespace RecipeFieldSpU

open Matrix CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag
  CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher

variable {r : ℕ} {K : Type} [Field K]

@[expose] noncomputable def gspNorm (σ : K ≃+* K) (A : gsp r K) : ℕ → gsp r K
  | 0 => 1
  | j + 1 => A * gspFieldMap σ (gspNorm σ A j)

theorem coe_gspNorm (σ : K ≃+* K) (A : gsp r K) (j : ℕ) :
    (((gspNorm σ A j : gsp r K) : GL (Fin r ⊕ Fin r) K) :
      Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) =
      twNorm σ ((A : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) j := by
  induction j with
  | zero => rfl
  | succ j ih =>
    rw [twNorm_succ, ← ih]
    rfl

theorem conjAut_mul_fieldAut_pow (A : gsp r K) (σ : K ≃+* K) (j : ℕ) :
    (conjAut r K A * fieldAut r K σ) ^ j = conjAut r K (gspNorm σ A j) * fieldAut r K (σ ^ j) := by
  induction j with
  | zero => rw [pow_zero, pow_zero, map_one, gspNorm, map_one, one_mul]
  | succ j ih => rw [pow_succ', ih, conjAut_mul_fieldAut_mul, ← pow_succ']; rfl

theorem exists_gsp_mul_map_eq_smul [Finite K] (hr : 1 ≤ r) {σ : K ≃+* K} {h : ℕ}
    (hσ : orderOf σ = h) (A : gsp r K) {c : K}
    (hc : twNorm σ ((A : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) h =
      c • (1 : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K)) :
    ∃ (H : gsp r K) (d : Kˣ), (A : GL (Fin r ⊕ Fin r) K) *
      GeneralLinearGroup.map (σ : K →+* K) (H : GL (Fin r ⊕ Fin r) K) =
        GeneralLinearGroup.scalar (Fin r ⊕ Fin r) d * H := by
  classical
  have : Nonempty (Fin r ⊕ Fin r) := ⟨Sum.inl ⟨0, by omega⟩⟩
  have hσh : σ ^ h = 1 := by rw [← hσ, pow_orderOf_eq_one]
  set J : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K := formJ r K with hJ
  set M : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K :=
    ((A : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) with hM
  obtain ⟨X, d₁, hXu, hd₁0, hXσ⟩ :=
    exists_mul_map_eq_smul_of_twNorm hσ (Matrix.isUnits_det_units (A : GL (Fin r ⊕ Fin r) K)) hc
  set Mi : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K :=
    (((A : GL (Fin r ⊕ Fin r) K)⁻¹ : GL (Fin r ⊕ Fin r) K) :
      Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) with hMi
  obtain ⟨μA, hμA⟩ := A.2
  have hMiM : Mi * M = 1 := by rw [hMi, hM, ← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hMiJ : Miᵀ * J * Mi = ((μA⁻¹ : Kˣ) : K) • J := inv_transpose_formJ hμA
  have hXσ' : X.map σ = d₁ • (Mi * X) := by
    calc X.map σ = Mi * (M * X.map σ) := by rw [← Matrix.mul_assoc, hMiM, Matrix.one_mul]
      _ = _ := by rw [hXσ, Matrix.mul_smul]
  obtain ⟨B, hB⟩ : ∃ B : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K, B = Xᵀ * J * X := ⟨_, rfl⟩
  obtain ⟨μ, hμ⟩ : ∃ μ : K, μ = d₁ * d₁ * ((μA⁻¹ : Kˣ) : K) := ⟨_, rfl⟩
  have hBσ : B.map σ = μ • B := by
    have e1 : (Xᵀ * J * X).map σ = (X.map σ)ᵀ * J * X.map σ := by
      rw [map_mul_ringEquiv, map_mul_ringEquiv, ← Matrix.transpose_map, hJ,
        CFSG.RankThree.PartTwo.KFacts.formJ_map]
    have e2 : Xᵀ * Miᵀ * J * (Mi * X) = ((μA⁻¹ : Kˣ) : K) • (Xᵀ * J * X) := by
      calc Xᵀ * Miᵀ * J * (Mi * X) = Xᵀ * (Miᵀ * J * Mi) * X := by
            simp only [Matrix.mul_assoc]
        _ = ((μA⁻¹ : Kˣ) : K) • (Xᵀ * J * X) := by
            rw [hMiJ, Matrix.mul_smul, Matrix.smul_mul]
    rw [hB, e1, hXσ', Matrix.transpose_smul, Matrix.transpose_mul, Matrix.smul_mul,
      Matrix.smul_mul, Matrix.mul_smul, smul_smul, e2, smul_smul, hμ]
  have hXdet : X.det ≠ 0 := hXu.ne_zero
  have hJdet : J.det ≠ 0 := by
    rw [hJ, CFSG.RankThree.PartTwo.KFacts.formJ_eq_neg_J, Matrix.det_neg]
    exact mul_ne_zero (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero))
      (Matrix.isUnit_det_J (Fin r) K).ne_zero
  have hBdet : B.det ≠ 0 := by
    rw [hB, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose]
    exact mul_ne_zero (mul_ne_zero hXdet hJdet) hXdet
  have hB0 : B ≠ 0 := by
    intro h0
    rw [h0, Matrix.det_zero] at hBdet
    exact hBdet rfl
  have hμh : ∏ i ∈ Finset.range h, (σ ^ i) μ = 1 := by
    have h1 := map_pow_eq_prod_smul σ hBσ h
    have hone : B.map ⇑(σ ^ h) = B := by
      rw [hσh]
      ext i j
      rfl
    rw [hone] at h1
    exact smul_left_injective K hB0 (h1.symm.trans (one_smul K B).symm)
  have hμ0 : μ ≠ 0 := by
    rw [hμ]
    exact mul_ne_zero (mul_ne_zero hd₁0 hd₁0) (Units.ne_zero _)
  let a : K ≃+ K :=
    { toFun := fun x => μ * σ x
      invFun := fun x => σ.symm (μ⁻¹ * x)
      left_inv := fun x => by
        simp only
        rw [inv_mul_cancel_left₀ hμ0, RingEquiv.symm_apply_apply]
      right_inv := fun x => by
        simp only
        rw [RingEquiv.apply_symm_apply, mul_inv_cancel_left₀ hμ0]
      map_add' := fun x y => by simp only [map_add, mul_add] }
  have ha : ∀ (c v : K), a (c • v) = σ c • a v := fun c v => by
    change μ * σ (c * v) = σ c * (μ * σ v)
    rw [map_mul]
    ring
  have hah : ∀ v, (⇑a)^[h] v = v := fun v => by
    change (fun y : K => μ * σ y)^[h] v = v
    rw [iterate_mul_map_apply, hμh, one_mul, hσh]
    rfl
  have : Fintype K := Fintype.ofFinite K
  obtain ⟨ℓ, -, e, hℓ, hcard⟩ := FiniteField.card' K
  obtain ⟨-, k₀, hk₀, -, bt, hbt, -⟩ :=
    CFSG.RankThree.Classical.semilinear_fixed_basis hℓ e.pos
      (by rw [Nat.card_eq_fintype_card, hcard]) σ hσ (Module.finrank_self K) a ha hah
  have ht0 : bt 0 ≠ 0 := bt.ne_zero 0
  have hμt : μ * σ (bt 0) = bt 0 := hbt 0
  obtain ⟨B', hB'⟩ : ∃ B' : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K, B' = bt 0 • B :=
    ⟨_, rfl⟩
  have hB'σ : B'.map σ = B' := by
    rw [hB', map_smul_ringEquiv, hBσ, smul_smul,
      show σ (bt 0) * μ = bt 0 by rw [mul_comm]; exact hμt]
  have hk₀mem : ∀ x, x ∈ k₀ ↔ σ x = x := fun x => by
    rw [← SetLike.mem_coe, hk₀]
    rfl
  have hB'mem : ∀ i j, B' i j ∈ k₀ := fun i j =>
    (hk₀mem _).mpr (congrFun (congrFun hB'σ i) j)
  let B₀ : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) k₀ := fun i j => ⟨B' i j, hB'mem i j⟩
  have hB₀map : B₀.map k₀.subtype = B' := by
    ext i j
    rfl
  have hB'det : B'.det ≠ 0 := by
    rw [hB', Matrix.det_smul]
    exact mul_ne_zero (pow_ne_zero _ ht0) hBdet
  have hB₀det : B₀.det ≠ 0 := by
    intro h0
    apply hB'det
    rw [← hB₀map, ← RingHom.mapMatrix_apply, ← RingHom.map_det, h0, map_zero]
  have halt : (Matrix.toBilin' B₀).IsAlt := by
    intro x
    rw [Matrix.toBilin'_apply']
    apply k₀.subtype_injective
    rw [map_zero]
    have e3 : k₀.subtype (x ⬝ᵥ B₀ *ᵥ x) =
        (fun i => (x i : K)) ⬝ᵥ (B' *ᵥ fun i => (x i : K)) := by
      rw [← hB₀map]
      simp only [dotProduct, Matrix.mulVec, map_sum, map_mul, Matrix.map_apply]
      rfl
    rw [e3, hB', Matrix.smul_mulVec, dotProduct_smul, hB, ← Matrix.mulVec_mulVec,
      ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_transpose, hJ,
      CFSG.RankThree.PartTwo.KFacts.dotProduct_formJ_mulVec_self, smul_zero]
  have hnd : (Matrix.toBilin' B₀).Nondegenerate :=
    LinearMap.BilinForm.nondegenerate_toBilin'_of_det_ne_zero' B₀ hB₀det
  obtain ⟨m, bJ, hbJ⟩ := LinearMap.BilinForm.IsAlt.exists_basis_toMatrix_eq_J halt hnd
  have hm : m = r := by
    have h1 := Module.finrank_eq_card_basis bJ
    rw [Module.finrank_fintype_fun_eq_card] at h1
    simp only [Fintype.card_sum, Fintype.card_fin] at h1
    omega
  subst m
  set P₀ : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) k₀ :=
    (Pi.basisFun k₀ (Fin r ⊕ Fin r)).toMatrix bJ with hP₀def
  have hP₀ : P₀ᵀ * B₀ * P₀ = Matrix.J (Fin r) k₀ := by
    have h1 := LinearMap.BilinForm.toMatrix_mul_basis_toMatrix
      (Pi.basisFun k₀ (Fin r ⊕ Fin r)) bJ (Matrix.toBilin' B₀)
    rw [LinearMap.BilinForm.toMatrix_basisFun, LinearMap.BilinForm.toMatrix'_toBilin', hbJ] at h1
    exact h1
  have hP₀det : IsUnit P₀.det := by
    rw [hP₀def, ← Module.Basis.det_apply]
    exact (Pi.basisFun k₀ (Fin r ⊕ Fin r)).isUnit_det bJ
  obtain ⟨P, hP⟩ : ∃ P : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K, P = P₀.map k₀.subtype :=
    ⟨_, rfl⟩
  have hPσ : P.map σ = P := by
    rw [hP]
    ext i j
    exact (hk₀mem _).mp (P₀ i j).2
  have hPJ : Pᵀ * B' * P = Matrix.J (Fin r) K := by
    have h1 := congrArg k₀.subtype.mapMatrix hP₀
    rw [map_mul, map_mul, RingHom.mapMatrix_apply, RingHom.mapMatrix_apply,
      RingHom.mapMatrix_apply, Matrix.transpose_map, hB₀map, ← hP] at h1
    rw [h1]
    ext i j
    rcases i with i | i <;> rcases j with j | j <;> simp [Matrix.J, Matrix.one_apply] <;>
      split_ifs <;> simp
  set Xgl : GL (Fin r ⊕ Fin r) K := ((Matrix.isUnit_iff_isUnit_det X).mpr hXu).unit with hXgl
  set Hgl : GL (Fin r ⊕ Fin r) K := Xgl *
    Matrix.GeneralLinearGroup.map k₀.subtype ((Matrix.isUnit_iff_isUnit_det P₀).mpr hP₀det).unit
    with hHgl
  have hHmat : (Hgl : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) = X * P := by
    rw [hHgl, Units.val_mul, hP, hXgl]
    rfl
  have hmu0 : (-(bt 0)⁻¹ : K) ≠ 0 := neg_ne_zero.mpr (inv_ne_zero ht0)
  have hHgsp : Hgl ∈ gsp r K := by
    refine ⟨Units.mk0 _ hmu0, ?_⟩
    rw [hHmat, Units.val_mk0, Matrix.transpose_mul]
    calc Pᵀ * Xᵀ * formJ r K * (X * P) = Pᵀ * B * P := by
          rw [hB, hJ]
          simp only [Matrix.mul_assoc]
      _ = (bt 0)⁻¹ • (Pᵀ * B' * P) := by
          rw [hB', Matrix.mul_smul, Matrix.smul_mul, smul_smul, inv_mul_cancel₀ ht0, one_smul]
      _ = (-(bt 0)⁻¹) • formJ r K := by
          rw [hPJ, CFSG.RankThree.PartTwo.KFacts.formJ_eq_neg_J, smul_neg, neg_smul, neg_neg]
  refine ⟨⟨Hgl, hHgsp⟩, Units.mk0 d₁ hd₁0, ?_⟩
  apply Units.ext
  change M * ((Hgl : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K).map σ) =
    Matrix.scalar (Fin r ⊕ Fin r) d₁ * (Hgl : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K)
  rw [hHmat, map_mul_ringEquiv, hPσ, ← Matrix.mul_assoc, hXσ, Matrix.scalar_apply,
    ← smul_eq_diagonal_mul, Matrix.smul_mul]

theorem conjAut_mul_fieldAut_of_pow_eq_one [Finite K] (hr : 1 ≤ r) {ℓ : ℕ} (hℓ : ℓ.Prime)
    (A : gsp r K) (σ : K ≃+* K) (hσ1 : σ ≠ 1) (hα : (conjAut r K A * fieldAut r K σ) ^ ℓ = 1) :
    orderOf σ = ℓ ∧ ∃ H : gsp r K,
      conjAut r K A * fieldAut r K σ = conjAut r K H * fieldAut r K σ * (conjAut r K H)⁻¹ := by
  rw [conjAut_mul_fieldAut_pow] at hα
  have hf : fieldAut r K (σ ^ ℓ) ∈ (conjAut r K).range :=
    ⟨(gspNorm σ A ℓ)⁻¹, by
      rw [map_inv]
      exact (eq_inv_of_mul_eq_one_right hα).symm⟩
  have hσℓ := (CFSG.RankThree.PartTwo.KFacts.fieldAut_mem_range_conjAut_iff hr).mp hf
  have hσo : orderOf σ = ℓ := by
    have : Fact ℓ.Prime := ⟨hℓ⟩
    exact orderOf_eq_prime hσℓ hσ1
  rw [hσℓ, map_one, mul_one] at hα
  obtain ⟨c, hc⟩ := CFSG.RankThree.PartTwo.KFacts.exists_scalar_of_conjAut_eq_one hr hα
  have hc' : twNorm σ ((A : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) ℓ =
      (c : K) • (1 : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) := by
    rw [← coe_gspNorm, hc, GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
      smul_one_eq_diagonal]
  obtain ⟨H, d, hH⟩ := exists_gsp_mul_map_eq_smul hr hσo A hc'
  refine ⟨hσo, H, ?_⟩
  have hAeq : A = ⟨_, CFSG.RankThree.PartTwo.KFacts.scalar_mem_gsp d⟩ * H * (gspFieldMap σ H)⁻¹ :=
    Subtype.ext (eq_mul_inv_of_mul_eq hH)
  rw [hAeq, map_mul, map_mul, map_inv, CFSG.RankThree.PartTwo.KFacts.conjAut_scalar_eq_one,
    one_mul, ← fieldAut_mul_conjAut_mul_inv σ H]
  group

end RecipeFieldSpU

end CFSG.StandardType
