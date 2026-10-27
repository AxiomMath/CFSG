module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PSL2RootGroups

namespace CFSG
end CFSG
open CFSG

/-!
# Affine coordinates on the projective line of `PSL₂`

The complement of infinity in the projective line is canonically identified
with the coefficient field by `x ↦ ⟨(x,1)⟩`.  In these coordinates the
standard upper-unipotent root group acts by translations.
-/

noncomputable section

namespace CFSG.GorensteinWalter

open Matrix Projectivization
open scoped LinearAlgebra.Projectivization MatrixGroups

universe u

public theorem psl2AffineVector_ne_zero
    {K : Type u} [Field K] (x : K) :
    (![x, 1] : Fin 2 → K) ≠ 0 := by
  intro h
  have := congrFun h 1
  simp at this

/-- The affine projective point with coordinate `x`. -/
@[expose]
public def psl2AffinePoint
    (K : Type u) [Field K] (x : K) : PSL2ProjectiveLine K :=
  Projectivization.mk K ![x, 1] (psl2AffineVector_ne_zero x)

public theorem psl2AffinePoint_injective
    {K : Type u} [Field K] :
    Function.Injective (psl2AffinePoint K) := by
  intro x y hxy
  rw [psl2AffinePoint, psl2AffinePoint,
    Projectivization.mk_eq_mk_iff] at hxy
  obtain ⟨a, ha⟩ := hxy
  have ha1 : (a : K) = 1 := by
    simpa [Units.smul_def] using congrFun ha 1
  have h0 := congrFun ha 0
  simpa [Units.smul_def, ha1] using h0.symm

public theorem psl2AffinePoint_ne_infinity
    {K : Type u} [Field K] (x : K) :
    psl2AffinePoint K x ≠ psl2ProjectiveInfinity K := by
  intro h
  rw [psl2AffinePoint, psl2ProjectiveInfinity,
    Projectivization.mk_eq_mk_iff] at h
  obtain ⟨a, ha⟩ := h
  have h1 := congrFun ha 1
  simpa [Units.smul_def] using h1.symm

@[simp]
public theorem psl2AffinePoint_zero
    {K : Type u} [Field K] :
    psl2AffinePoint K 0 = psl2ProjectiveZero K := by
  rw [psl2AffinePoint, psl2ProjectiveZero]

/-- Every non-infinity point has a unique affine coordinate. -/
public theorem existsUnique_psl2AffinePoint_eq
    {K : Type u} [Field K]
    (p : PSL2ProjectiveLine K)
    (hp : p ≠ psl2ProjectiveInfinity K) :
    ∃! x : K, psl2AffinePoint K x = p := by
  induction p using Projectivization.ind with
  | h v hv =>
      have hv1 : v 1 ≠ 0 := by
        intro hv1
        apply hp
        rw [psl2ProjectiveInfinity,
          Projectivization.mk_eq_mk_iff']
        refine ⟨v 0, ?_⟩
        ext i
        fin_cases i <;> simp [hv1]
      have hx : psl2AffinePoint K (v 0 / v 1) =
          Projectivization.mk K v hv := by
        rw [psl2AffinePoint, Projectivization.mk_eq_mk_iff']
        refine ⟨(v 1)⁻¹, ?_⟩
        ext i
        fin_cases i <;>
          simp [div_eq_mul_inv, hv1, mul_comm]
      refine ⟨v 0 / v 1, hx, ?_⟩
      intro y hy
      exact psl2AffinePoint_injective (hy.trans hx.symm)

/-- The affine coordinate equivalence from the field to the complement of
infinity. -/
@[expose]
public noncomputable def psl2AffineEquiv
    (K : Type u) [Field K] :
    K ≃ {p : PSL2ProjectiveLine K // p ≠ psl2ProjectiveInfinity K} :=
  Equiv.ofBijective
    (fun x => ⟨psl2AffinePoint K x, psl2AffinePoint_ne_infinity x⟩)
    ⟨fun x y h => psl2AffinePoint_injective (congrArg Subtype.val h),
      fun p => by
        obtain ⟨x, hx, _⟩ :=
          existsUnique_psl2AffinePoint_eq
            (p : PSL2ProjectiveLine K) p.property
        exact ⟨x, Subtype.ext hx⟩⟩

@[simp]
public theorem psl2AffineEquiv_apply
    (K : Type u) [Field K] (x : K) :
    (psl2AffineEquiv K x : PSL2ProjectiveLine K) =
      psl2AffinePoint K x := rfl

/-- Upper-unipotent matrices act by translations in the affine coordinate
chart. -/
@[simp]
public theorem psl2UpperUnipotent_smul_affine
    {K : Type u} [Field K] (a x : K) :
  psl2QuotientMap K (sl2UpperUnipotent a) • psl2AffinePoint K x =
      psl2AffinePoint K (x + a) := by
  rw [psl2QuotientMap_smul, psl2AffinePoint,
    Projectivization.smul_mk]
  change Projectivization.mk K
      ((sl2UpperUnipotent a).val *ᵥ ![x, 1]) _ =
    Projectivization.mk K ![x + a, 1] _
  rw [Projectivization.mk_eq_mk_iff']
  refine ⟨1, ?_⟩
  change (1 : K) • (![x + a, 1] : Fin 2 → K) =
    (sl2UpperUnipotent a).val *ᵥ ![x, 1]
  ext i
  fin_cases i <;>
    simp [sl2UpperUnipotent, Matrix.mulVec, Matrix.vecHead,
      Matrix.vecTail, add_comm]

/-- A determinant-one diagonal matrix acts on affine coordinates by
multiplication by the square of its upper-left entry. -/
public theorem psl2Diag2_smul_affine
    {K : Type u} [Field K] (t : K) (ht : t ≠ 0) (x : K) :
    psl2QuotientMap K (Matrix.SpecialLinearGroup.diag2 t ht) •
        psl2AffinePoint K x =
      psl2AffinePoint K (t ^ 2 * x) := by
  rw [psl2QuotientMap_smul, psl2AffinePoint,
    Projectivization.smul_mk]
  change Projectivization.mk K
      ((Matrix.SpecialLinearGroup.diag2 t ht).val *ᵥ ![x, 1]) _ =
    Projectivization.mk K ![t ^ 2 * x, 1] _
  rw [Projectivization.mk_eq_mk_iff']
  refine ⟨Units.mk0 t⁻¹ (inv_ne_zero ht), ?_⟩
  change (t⁻¹ : K) • (![t ^ 2 * x, 1] : Fin 2 → K) =
    (Matrix.SpecialLinearGroup.diag2 t ht).val *ᵥ ![x, 1]
  ext i
  fin_cases i <;>
    simp [Matrix.SpecialLinearGroup.diag2_coe', Matrix.mulVec,
      Matrix.vecHead, Matrix.vecTail, sq, ht,
      mul_assoc]

/-- An element of `PSL₂(K)` fixing both infinity and zero acts on the affine
chart by multiplication by a field scalar. -/
public theorem exists_psl2_smul_affine_eq_mul_of_fixes_infinity_zero
    {K : Type u} [Field K]
    (g : PSL2 K)
    (hInfinity : g • psl2ProjectiveInfinity K =
      psl2ProjectiveInfinity K)
    (hZero : g • psl2ProjectiveZero K = psl2ProjectiveZero K) :
    ∃ c : K, ∀ x : K,
      g • psl2AffinePoint K x = psl2AffinePoint K (c * x) := by
  obtain ⟨A, rfl⟩ := psl2QuotientMap_surjective (K := K) g
  have hAInfinity : A ∈
      MulAction.stabilizer (SL(2, K)) (psl2ProjectiveInfinity K) := by
    rw [MulAction.mem_stabilizer_iff]
    exact hInfinity
  have hAZero : A ∈
      MulAction.stabilizer (SL(2, K)) (psl2ProjectiveZero K) := by
    rw [MulAction.mem_stabilizer_iff]
    exact hZero
  have h10 : A.val 1 0 = 0 :=
    (sl2_mem_stabilizer_infinity_iff A).1 hAInfinity
  have h01 : A.val 0 1 = 0 :=
    (sl2_mem_stabilizer_zero_iff A).1 hAZero
  have hdet : A.val 0 0 * A.val 1 1 = 1 := by
    have h := A.property
    rw [Matrix.det_fin_two, h10, h01] at h
    simpa using h
  have h00 : A.val 0 0 ≠ 0 := left_ne_zero_of_mul_eq_one hdet
  have h11 : A.val 1 1 = (A.val 0 0)⁻¹ :=
    eq_inv_of_mul_eq_one_left (by rw [mul_comm]; exact hdet)
  refine ⟨A.val 0 0 ^ 2, fun x => ?_⟩
  rw [psl2QuotientMap_smul, psl2AffinePoint,
    Projectivization.smul_mk]
  change Projectivization.mk K (A.val *ᵥ ![x, 1]) _ =
    Projectivization.mk K ![A.val 0 0 ^ 2 * x, 1] _
  rw [Projectivization.mk_eq_mk_iff']
  refine ⟨Units.mk0 (A.val 0 0)⁻¹ (inv_ne_zero h00), ?_⟩
  change (A.val 0 0)⁻¹ •
      (![A.val 0 0 ^ 2 * x, 1] : Fin 2 → K) =
    A.val *ᵥ ![x, 1]
  ext i
  fin_cases i <;>
    simp [Matrix.mulVec, Matrix.vecHead, Matrix.vecTail,
      h10, h01, h11, sq, h00, mul_assoc]

end CFSG.GorensteinWalter
