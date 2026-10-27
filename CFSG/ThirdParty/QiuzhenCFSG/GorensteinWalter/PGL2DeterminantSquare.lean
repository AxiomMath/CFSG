module

public import Mathlib.LinearAlgebra.Projectivization.PSL.PSL2

namespace CFSG
end CFSG
open CFSG

/-!
# Determinant-square membership in `PGL₂`

A projective class belongs to the canonical embedded `PSL₂` precisely when
the determinant of any general-linear representative is a square.  This is
the concrete membership criterion needed to distinguish the two involution
classes in odd `PGL₂` torus normalizers.
-/

noncomputable section

namespace CFSG.GorensteinWalter

open Matrix
open scoped MatrixGroups

universe u

/-- A class represented by `A : GL₂(K)` belongs to the canonical `PSL₂(K)`
image in `PGL₂(K)` if and only if `det A` is a square in `K`. -/
public theorem pgl2_mk_mem_psl2_range_iff_det_isSquare
    {K : Type u} [Field K]
    (A : GL (Fin 2) K) :
    Matrix.ProjGenLinGroup.mk A ∈
        (Matrix.ProjectiveSpecialLinearGroup.toPGL
          (n := Fin 2) (R := K)).range ↔
      IsSquare (A.det : K) := by
  classical
  constructor
  · rintro ⟨x, hx⟩
    obtain ⟨S, rfl⟩ := QuotientGroup.mk_surjective x
    rw [Matrix.ProjectiveSpecialLinearGroup.toPGL_mk] at hx
    rcases Matrix.ProjGenLinGroup.mk_eq_mk_iff.mp hx with ⟨u, hu⟩
    have hdet := congrArg Matrix.GeneralLinearGroup.det hu
    have hdetS : Matrix.GeneralLinearGroup.det
        (Matrix.SpecialLinearGroup.toGL S) = 1 := by
      apply Units.ext
      exact Matrix.SpecialLinearGroup.det_coe S
    rw [map_mul, hdetS, one_mul,
      Matrix.GeneralLinearGroup.det_scalar] at hdet
    refine ⟨(u : K), ?_⟩
    simpa [pow_two] using congrArg Units.val hdet.symm
  · rintro ⟨d, hd⟩
    have hd_ne : d ≠ 0 := by
      intro hd0
      apply Units.ne_zero A.det
      rw [hd, hd0]
      simp
    let dU : Kˣ := Units.mk0 d hd_ne
    let B : GL (Fin 2) K :=
      Matrix.GeneralLinearGroup.scalar (Fin 2) dU⁻¹ * A
    have hBdetUnit : Matrix.GeneralLinearGroup.det B = 1 := by
      dsimp [B]
      rw [map_mul, Matrix.GeneralLinearGroup.det_scalar]
      apply Units.ext
      change d⁻¹ ^ 2 * (A.det : K) = 1
      rw [hd]
      field_simp
    have hBdet : Matrix.det (B : Matrix (Fin 2) (Fin 2) K) = 1 :=
      congrArg Units.val hBdetUnit
    let Bs : Matrix.SpecialLinearGroup (Fin 2) K :=
      ⟨(B : Matrix (Fin 2) (Fin 2) K), hBdet⟩
    refine ⟨QuotientGroup.mk Bs, ?_⟩
    rw [Matrix.ProjectiveSpecialLinearGroup.toPGL_mk]
    have htoGL : Matrix.SpecialLinearGroup.toGL Bs = B := by
      apply Matrix.GeneralLinearGroup.ext
      intro i j
      rfl
    rw [htoGL]
    dsimp [B]
    rw [map_mul, Matrix.ProjGenLinGroup.mk_scalar, one_mul]

end CFSG.GorensteinWalter
