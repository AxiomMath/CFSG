module

public import CFSG.LocalAnalysis.StandardType.GGSixPositionDefs
public import CFSG.LocalAnalysis.StandardType.ClassicalPosition.Defs
public import CFSG.LieType.Universal.SpecialLinearExtras

public section

namespace CFSG.StandardType.ClassicalPosition

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank CFSG.StandardType CFSG.StandardType.S2MathFi1035Pos
open Matrix

private theorem grcPSL_transvection_coe {m : ℕ} {F : Type} [Field F]
    {i j : Fin (m + 1)} (hij : i ≠ j) (b : F) :
    ((Matrix.SpecialLinearGroup.transvection hij b :
      Matrix.SpecialLinearGroup (Fin (m + 1)) F) :
      Matrix (Fin (m + 1)) (Fin (m + 1)) F) =
      1 + b • Matrix.vecMulVec (Pi.single i 1) (Pi.single j 1) := by
  rw [Matrix.SpecialLinearGroup.transvection_coe,
    show Matrix.single i j b = b • Matrix.single i j 1 by
      rw [Matrix.smul_single, smul_eq_mul, mul_one],
    Matrix.single_eq_single_vecMulVec_single]

private theorem grcPSL_conj_vecMulVec (m : ℕ) (F : Type) [Field F]
    (u : Matrix.SpecialLinearGroup (Fin (m + 1)) F)
    (x y x' y' : Fin (m + 1) → F) (c : F)
    (hx : (u : Matrix (Fin (m + 1)) (Fin (m + 1)) F) *ᵥ x = x')
    (hy : y ᵥ* ((u⁻¹ : Matrix.SpecialLinearGroup (Fin (m + 1)) F) :
      Matrix (Fin (m + 1)) (Fin (m + 1)) F) = y') :
    (u : Matrix (Fin (m + 1)) (Fin (m + 1)) F) *
        (1 + c • Matrix.vecMulVec x y) *
        ((u⁻¹ : Matrix.SpecialLinearGroup (Fin (m + 1)) F) :
          Matrix (Fin (m + 1)) (Fin (m + 1)) F) =
      1 + c • Matrix.vecMulVec x' y' := by
  have hwu : (u : Matrix (Fin (m + 1)) (Fin (m + 1)) F) *
      ((u⁻¹ : Matrix.SpecialLinearGroup (Fin (m + 1)) F) :
        Matrix (Fin (m + 1)) (Fin (m + 1)) F) = 1 := by
    rw [← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel, Matrix.SpecialLinearGroup.coe_one]
  rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, hwu, Matrix.mul_smul, Matrix.smul_mul,
    Matrix.mul_vecMulVec, Matrix.vecMulVec_mul, hx, hy]

private theorem grcPSL_map_conj (m : ℕ) (F : Type) [Field F]
    {i j : Fin (m + 1)} (hij : i ≠ j)
    {β : Fin m → ℤ} (hroot : SpecialLinear.toStd m β = Pi.single i 1 - Pi.single j 1)
    (u : Matrix.SpecialLinearGroup (Fin (m + 1)) F)
    (M : Matrix (Fin (m + 1)) (Fin (m + 1)) F)
    (hconj : ∀ c : F, (u : Matrix (Fin (m + 1)) (Fin (m + 1)) F) *
        (1 + c • Matrix.vecMulVec (Pi.single i 1) (Pi.single j 1)) *
        ((u⁻¹ : Matrix.SpecialLinearGroup (Fin (m + 1)) F) :
          Matrix (Fin (m + 1)) (Fin (m + 1)) F) = 1 + c • M) :
    (((SpecialLinear.rootGroup m F β).map (MulAut.conj u).toMonoidHom).map
        Matrix.SpecialLinearGroup.toGL) =
      Subgroup.closure {g : GL (Fin (m + 1)) F | ∃ c : F,
        (g : Matrix (Fin (m + 1)) (Fin (m + 1)) F) = 1 + c • M} := by
  rw [SpecialLinear.rootGroup_eq m F hij hroot]
  apply le_antisymm
  · rintro g ⟨x, hx, rfl⟩
    change x ∈ Subgroup.map (MulEquiv.toMonoidHom (MulAut.conj u))
      (SpecialLinear.rootSubgroup m F hij) at hx
    rw [Subgroup.mem_map] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    rw [SpecialLinear.mem_rootSubgroup] at hy
    obtain ⟨c, rfl⟩ := hy
    refine Subgroup.subset_closure ⟨c, ?_⟩
    have hcoe : ((Matrix.SpecialLinearGroup.toGL
        ((MulAut.conj u) (Matrix.SpecialLinearGroup.transvection hij c)) :
          GL (Fin (m + 1)) F) : Matrix (Fin (m + 1)) (Fin (m + 1)) F) =
        (u : Matrix (Fin (m + 1)) (Fin (m + 1)) F) *
          (1 + c • Matrix.vecMulVec (Pi.single i 1) (Pi.single j 1)) *
          ((u⁻¹ : Matrix.SpecialLinearGroup (Fin (m + 1)) F) :
            Matrix (Fin (m + 1)) (Fin (m + 1)) F) := by
      rw [MulAut.conj_apply, map_mul, map_mul]
      change (u : Matrix (Fin (m + 1)) (Fin (m + 1)) F) *
          ((Matrix.SpecialLinearGroup.transvection hij c :
            Matrix.SpecialLinearGroup (Fin (m + 1)) F) :
            Matrix (Fin (m + 1)) (Fin (m + 1)) F) *
          ((u⁻¹ : Matrix.SpecialLinearGroup (Fin (m + 1)) F) :
            Matrix (Fin (m + 1)) (Fin (m + 1)) F) = _
      rw [grcPSL_transvection_coe hij c]
    exact hcoe.trans (hconj c)
  · rw [Subgroup.closure_le]
    rintro g ⟨c, hc⟩
    change g ∈ Subgroup.map Matrix.SpecialLinearGroup.toGL
      (Subgroup.map (MulEquiv.toMonoidHom (MulAut.conj u)) (SpecialLinear.rootSubgroup m F hij))
    rw [Subgroup.mem_map]
    refine ⟨(MulAut.conj u) (Matrix.SpecialLinearGroup.transvection hij c), ?_, ?_⟩
    · change (MulAut.conj u) (Matrix.SpecialLinearGroup.transvection hij c) ∈
        Subgroup.map (MulEquiv.toMonoidHom (MulAut.conj u)) (SpecialLinear.rootSubgroup m F hij)
      rw [Subgroup.mem_map]
      exact ⟨Matrix.SpecialLinearGroup.transvection hij c,
        SpecialLinear.transvection_mem_rootSubgroup hij c, rfl⟩
    · apply Units.ext
      have hcoe : ((Matrix.SpecialLinearGroup.toGL
          ((MulAut.conj u) (Matrix.SpecialLinearGroup.transvection hij c)) :
            GL (Fin (m + 1)) F) : Matrix (Fin (m + 1)) (Fin (m + 1)) F) =
          (u : Matrix (Fin (m + 1)) (Fin (m + 1)) F) *
            (1 + c • Matrix.vecMulVec (Pi.single i 1) (Pi.single j 1)) *
            ((u⁻¹ : Matrix.SpecialLinearGroup (Fin (m + 1)) F) :
              Matrix (Fin (m + 1)) (Fin (m + 1)) F) := by
        rw [MulAut.conj_apply, map_mul, map_mul]
        change (u : Matrix (Fin (m + 1)) (Fin (m + 1)) F) *
            ((Matrix.SpecialLinearGroup.transvection hij c :
              Matrix.SpecialLinearGroup (Fin (m + 1)) F) :
              Matrix (Fin (m + 1)) (Fin (m + 1)) F) *
            ((u⁻¹ : Matrix.SpecialLinearGroup (Fin (m + 1)) F) :
              Matrix (Fin (m + 1)) (Fin (m + 1)) F) = _
        rw [grcPSL_transvection_coe hij c]
      rw [hcoe, hconj c]
      exact hc.symm

private theorem grcPSL_root_std_form (m : ℕ) (F : Type) [Field F] {β : Fin m → ℤ}
    (hβ : β ∈ (SpecialLinear.rootDatum m F).roots) :
    ∃ i j : Fin (m + 1), i ≠ j ∧
      SpecialLinear.toStd m β = Pi.single i 1 - Pi.single j 1 := by
  have hβ' : β ∈ roots (SpecialLinear.isFiniteType_A m) ∅ := hβ
  rw [SpecialLinear.roots_eq] at hβ'
  exact hβ'

private theorem grcPSL_inv_mulVec_mulVec (m : ℕ) (F : Type) [Field F]
    (u : Matrix.SpecialLinearGroup (Fin (m + 1)) F) (w : Fin (m + 1) → F) :
    ((u⁻¹ : Matrix.SpecialLinearGroup (Fin (m + 1)) F) :
        Matrix (Fin (m + 1)) (Fin (m + 1)) F) *ᵥ
      ((u : Matrix (Fin (m + 1)) (Fin (m + 1)) F) *ᵥ w) = w := by
  have h : ((u⁻¹ : Matrix.SpecialLinearGroup (Fin (m + 1)) F) :
      Matrix (Fin (m + 1)) (Fin (m + 1)) F) *
      (u : Matrix (Fin (m + 1)) (Fin (m + 1)) F) = 1 := by
    rw [← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel,
      Matrix.SpecialLinearGroup.coe_one]
  rw [Matrix.mulVec_mulVec, h, Matrix.one_mulVec]

private theorem grcPSL_mulVec_single_ne_zero (m : ℕ) (F : Type) [Field F]
    (u : Matrix.SpecialLinearGroup (Fin (m + 1)) F) (i : Fin (m + 1)) :
    (u : Matrix (Fin (m + 1)) (Fin (m + 1)) F) *ᵥ
      (Pi.single i 1 : Fin (m + 1) → F) ≠ 0 := by
  intro h0
  have h := grcPSL_inv_mulVec_mulVec m F u (Pi.single i 1 : Fin (m + 1) → F)
  rw [h0, Matrix.mulVec_zero] at h
  have h2 := congrFun h i
  rw [Pi.zero_apply, Pi.single_eq_same] at h2
  exact one_ne_zero h2.symm

private theorem grcPSL_vecMul_single_ne_zero (m : ℕ) (F : Type) [Field F]
    (u : Matrix.SpecialLinearGroup (Fin (m + 1)) F) (j : Fin (m + 1)) :
    (Pi.single j 1 : Fin (m + 1) → F) ᵥ*
      ((u⁻¹ : Matrix.SpecialLinearGroup (Fin (m + 1)) F) :
        Matrix (Fin (m + 1)) (Fin (m + 1)) F) ≠ 0 := by
  intro h0
  have h1 : ((Pi.single j 1 : Fin (m + 1) → F) ᵥ*
      ((u⁻¹ : Matrix.SpecialLinearGroup (Fin (m + 1)) F) :
        Matrix (Fin (m + 1)) (Fin (m + 1)) F)) ⬝ᵥ
      ((u : Matrix (Fin (m + 1)) (Fin (m + 1)) F) *ᵥ
        (Pi.single j 1 : Fin (m + 1) → F)) = 1 := by
    rw [← Matrix.dotProduct_mulVec]
    rw [grcPSL_inv_mulVec_mulVec m F u (Pi.single j 1 : Fin (m + 1) → F)]
    rw [dotProduct_single, Pi.single_eq_same, mul_one]
  rw [h0, zero_dotProduct] at h1
  exact one_ne_zero h1.symm

private theorem grcPSL_dot_row_col (m : ℕ) (F : Type) [Field F]
    {i j : Fin (m + 1)} (hij : i ≠ j)
    (u : Matrix.SpecialLinearGroup (Fin (m + 1)) F) :
    ((Pi.single j 1 : Fin (m + 1) → F) ᵥ*
        ((u⁻¹ : Matrix.SpecialLinearGroup (Fin (m + 1)) F) :
          Matrix (Fin (m + 1)) (Fin (m + 1)) F)) ⬝ᵥ
      ((u : Matrix (Fin (m + 1)) (Fin (m + 1)) F) *ᵥ
        (Pi.single i 1 : Fin (m + 1) → F)) = 0 := by
  rw [← Matrix.dotProduct_mulVec]
  rw [grcPSL_inv_mulVec_mulVec m F u (Pi.single i 1 : Fin (m + 1) → F)]
  rw [dotProduct_single, Pi.single_eq_of_ne hij, zero_mul]

private theorem grcPSL_conj_rootGroup_eq_matTransvGroup (m : ℕ) (F : Type) [Field F]
    {i j : Fin (m + 1)} (hij : i ≠ j) {β : Fin m → ℤ}
    (hstd : SpecialLinear.toStd m β = Pi.single i 1 - Pi.single j 1)
    (u : Matrix.SpecialLinearGroup (Fin (m + 1)) F) :
    (((SpecialLinear.rootDatum m F).rootGroup β).map (MulAut.conj u).toMonoidHom).map
        Matrix.SpecialLinearGroup.toGL =
      matTransvGroup
        ((u : Matrix (Fin (m + 1)) (Fin (m + 1)) F) *ᵥ
          (Pi.single i 1 : Fin (m + 1) → F))
        ((Pi.single j 1 : Fin (m + 1) → F) ᵥ*
          ((u⁻¹ : Matrix.SpecialLinearGroup (Fin (m + 1)) F) :
            Matrix (Fin (m + 1)) (Fin (m + 1)) F)) := by
  let v : Fin (m + 1) → F :=
    (u : Matrix (Fin (m + 1)) (Fin (m + 1)) F) *ᵥ (Pi.single i 1 : Fin (m + 1) → F)
  let φ : Fin (m + 1) → F :=
    (Pi.single j 1 : Fin (m + 1) → F) ᵥ*
      ((u⁻¹ : Matrix.SpecialLinearGroup (Fin (m + 1)) F) :
        Matrix (Fin (m + 1)) (Fin (m + 1)) F)
  change (((SpecialLinear.rootGroup m F β).map (MulAut.conj u).toMonoidHom).map
      Matrix.SpecialLinearGroup.toGL) = matTransvGroup v φ
  rw [grcPSL_map_conj m F hij hstd u (Matrix.vecMulVec v φ)
    (fun c => grcPSL_conj_vecMulVec m F u (Pi.single i 1) (Pi.single j 1) v φ c
      (rfl) (rfl))]
  rfl

theorem exists_matTransvGroup_eq_rootGroup_PSL (m : ℕ) (F : Type) [Field F]
    {β : Fin m → ℤ} (hβ : β ∈ (SpecialLinear.rootDatum m F).roots)
    (u : Matrix.SpecialLinearGroup (Fin (m + 1)) F) :
    ∃ v φ : Fin (m + 1) → F, v ≠ 0 ∧ φ ≠ 0 ∧ φ ⬝ᵥ v = 0 ∧
      (((SpecialLinear.rootDatum m F).rootGroup β).map (MulAut.conj u).toMonoidHom).map
        Matrix.SpecialLinearGroup.toGL = matTransvGroup v φ := by
  obtain ⟨i, j, hij, hstd⟩ := grcPSL_root_std_form m F hβ
  refine ⟨(u : Matrix (Fin (m + 1)) (Fin (m + 1)) F) *ᵥ
      (Pi.single i 1 : Fin (m + 1) → F),
    (Pi.single j 1 : Fin (m + 1) → F) ᵥ*
      ((u⁻¹ : Matrix.SpecialLinearGroup (Fin (m + 1)) F) :
        Matrix (Fin (m + 1)) (Fin (m + 1)) F), ?_, ?_, ?_, ?_⟩
  · exact grcPSL_mulVec_single_ne_zero m F u i
  · exact grcPSL_vecMul_single_ne_zero m F u j
  · exact grcPSL_dot_row_col m F hij u
  · exact grcPSL_conj_rootGroup_eq_matTransvGroup m F hij hstd u

end CFSG.StandardType.ClassicalPosition
