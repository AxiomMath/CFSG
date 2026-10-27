module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive.Invol.SpHeis

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive

open CFSG.Open Subgroup Matrix
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher (formJ gsp conjAut fieldAut)
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag (proj)

variable {r : ℕ} {K : Type} [Field K]

theorem spT_map (σ : K ≃+* K) (c a : Fin r ⊕ Fin r → K) :
    (spT c a).map σ = spT (fun i => σ (c i)) (fun i => σ (a i)) := by
  ext i j
  simp only [spT, Matrix.map_apply, vecMulVec_apply, map_mul]
  have h := RingHom.map_mulVec (σ : K →+* K) (formJ r K) c j
  rw [RingEquiv.coe_toRingHom,
    CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher.formJ_map] at h
  rw [h]
  rfl

theorem spN_map (σ : K ≃+* K) (a c : Fin r ⊕ Fin r → K) :
    (spN a c).map σ = spN (fun i => σ (a i)) (fun i => σ (c i)) := by
  rw [spN, Matrix.map_add _ (map_add σ), spT_map, spT_map, spN]

theorem spForm_mulVec {A : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K} {μ : K}
    (hA : Aᵀ * formJ r K * A = μ • formJ r K) (y z : Fin r ⊕ Fin r → K) :
    spForm (A *ᵥ y) (A *ᵥ z) = μ * spForm y z := by
  simp only [spForm]
  rw [mulVec_mulVec, dotProduct_mulVec, ← vecMul_transpose, vecMul_vecMul, ← Matrix.mul_assoc,
    hA, ← dotProduct_mulVec, smul_mulVec, dotProduct_smul, smul_eq_mul]

theorem conj_spT (A : GL (Fin r ⊕ Fin r) K) {μ : K}
    (hA : (A : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K)ᵀ * formJ r K * A = μ • formJ r K)
    (c a : Fin r ⊕ Fin r → K) :
    (A : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) * spT c a *
      ((A⁻¹ : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) =
      μ⁻¹ • spT ((A : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) *ᵥ c)
        ((A : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) *ᵥ a) := by
  rcases Nat.eq_zero_or_pos r with hr0 | hr
  · subst hr0
    exact Subsingleton.elim _ _
  have hμ : μ ≠ 0 := by
    intro hμ0
    have hA0 : (A : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K)ᵀ * formJ r K *
        (A : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) = 0 := by
      rw [hA, hμ0, zero_smul]
    have hJ0 : formJ r K = 0 := by
      rw [Matrix.ext_iff_mulVec]
      intro z
      have hz : (A : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) *ᵥ
          (((A⁻¹ : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) *ᵥ z)
            = z := by
        rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one,
          Matrix.one_mulVec]
      have h2 : ((A : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K)ᵀ * formJ r K *
          (A : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K)) *ᵥ
          (((A⁻¹ : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) *ᵥ z)
            = 0 := by
        rw [hA0, Matrix.zero_mulVec]
      rw [show ((A : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K)ᵀ * formJ r K *
          (A : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K)) *ᵥ
          (((A⁻¹ : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) *ᵥ z)
            = (A : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K)ᵀ *ᵥ (formJ r K *ᵥ z) by
        rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hz]] at h2
      have h3 : (((A⁻¹ : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K))ᵀ
          *ᵥ ((A : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K)ᵀ *ᵥ (formJ r K *ᵥ z)) = 0 := by
        rw [h2, Matrix.mulVec_zero]
      rw [Matrix.mulVec_mulVec, ← Matrix.transpose_mul, ← Units.val_mul, mul_inv_cancel,
        Units.val_one, Matrix.transpose_one, Matrix.one_mulVec] at h3
      simpa using h3
    obtain ⟨i⟩ : Nonempty (Fin r) := ⟨⟨0, hr⟩⟩
    have hentry : (1 : K) = 0 := by
      have h := congrFun (congrFun hJ0 (Sum.inl i)) (Sum.inr i)
      simp [formJ] at h
    exact one_ne_zero hentry
  rw [Matrix.ext_iff_mulVec]
  intro y
  have hAy : (A : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) *ᵥ
      (((A⁻¹ : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) *ᵥ y)
        = y := by
    rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one,
      Matrix.one_mulVec]
  have hkey : spForm
      (((A⁻¹ : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) *ᵥ y) c =
      μ⁻¹ * spForm y ((A : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) *ᵥ c) := by
    have h1 := spForm_mulVec hA
      (((A⁻¹ : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) *ᵥ y) c
    rw [hAy] at h1
    rw [h1, ← mul_assoc, inv_mul_cancel₀ hμ, one_mul]
  calc
    ((A : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) * spT c a *
        ((A⁻¹ : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K)) *ᵥ y
        = (A : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) *ᵥ (spT c a *ᵥ
            (((A⁻¹ : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) *ᵥ y)) := by
          rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
    _ = (A : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) *ᵥ
          (spForm (((A⁻¹ : GL (Fin r ⊕ Fin r) K) :
            Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) *ᵥ y) c • a) := by
          rw [spT_mulVec]
    _ = spForm (((A⁻¹ : GL (Fin r ⊕ Fin r) K) :
          Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) *ᵥ y) c •
          ((A : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) *ᵥ a) := by
          rw [Matrix.mulVec_smul]
    _ = (μ⁻¹ * spForm y ((A : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) *ᵥ c)) •
          ((A : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) *ᵥ a) := by
          rw [hkey]
    _ = (μ⁻¹ • spT ((A : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) *ᵥ c)
          ((A : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) *ᵥ a)) *ᵥ y := by
          rw [Matrix.smul_mulVec, spT_mulVec, smul_smul]

theorem conj_spN (A : GL (Fin r ⊕ Fin r) K) {μ : K}
    (hA : (A : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K)ᵀ * formJ r K * A = μ • formJ r K)
    (a c : Fin r ⊕ Fin r → K) :
    (A : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) * spN a c *
      ((A⁻¹ : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) =
      μ⁻¹ • spN ((A : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) *ᵥ a)
        ((A : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) *ᵥ c) := by
  rw [spN, Matrix.mul_add, Matrix.add_mul, conj_spT A hA, conj_spT A hA, spN, smul_add]

theorem conjAut_fieldAut_unipSp (A : gsp r K) (σ : K ≃+* K)
    {N N' : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K}
    (hs : Nᵀ * formJ r K + formJ r K * N = 0) (hN : N * N = 0)
    (hs' : N'ᵀ * formJ r K + formJ r K * N' = 0) (hN' : N' * N' = 0)
    (h : ((A : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) * N.map σ *
      (((A : GL (Fin r ⊕ Fin r) K)⁻¹ : GL (Fin r ⊕ Fin r) K) :
        Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) = N') :
    (conjAut r K A * fieldAut r K σ) (proj r K (unipSp N hs hN)) =
      proj r K (unipSp N' hs' hN') := by
  rw [MulAut.mul_apply, CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher.fieldAut_proj,
    CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher.conjAut_proj]
  congr 1
  apply CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl.statedSp_ext
  have hAA : ((A : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) *
      (((A : GL (Fin r ⊕ Fin r) K)⁻¹ : GL (Fin r ⊕ Fin r) K) :
        Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  rw [CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher.coe_conjSp, Units.val_mul,
    Units.val_mul, CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher.coe_fieldSp,
    coe_unipSp, coe_unipSp,
    Matrix.map_add (σ : K → K) (map_add σ),
    Matrix.map_one (σ : K → K) (map_zero σ) (map_one σ),
    Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, h, hAA]

theorem exists_inv_of_unipSp (A : gsp r K) (σ : K ≃+* K) {p : ℕ}
    {N : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K}
    (hs : Nᵀ * formJ r K + formJ r K * N = 0) (hN : N * N = 0)
    (h : ((A : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) * N.map σ *
      (((A : GL (Fin r ⊕ Fin r) K)⁻¹ : GL (Fin r ⊕ Fin r) K) :
        Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) = -N)
    (hgood : orderOf (proj r K (unipSp N hs hN)) = p ∧
      IsSpecialGood p (proj r K (unipSp N hs hN))) :
    ∃ x : StatedProj (StatedSp r K), orderOf x = p ∧
      (conjAut r K A * fieldAut r K σ) x = x⁻¹ ∧ (IsSpecialGood p x ∨ IsOrbitGood p x) := by
  refine ⟨proj r K (unipSp N hs hN), hgood.1, ?_, Or.inl hgood.2⟩
  rw [conjAut_fieldAut_unipSp A σ hs hN (isSp_neg hs) (neg_mul_self_neg hN) h, ← map_inv,
    unipSp_inv]

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive
