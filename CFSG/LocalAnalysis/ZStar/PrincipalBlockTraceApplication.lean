module

public import CFSG.LocalAnalysis.ZStar.GroupAlgebraTwistedTrace
public import CFSG.LocalAnalysis.ZStar.PadicBlockField
public import CFSG.LocalAnalysis.ZStar.IntegralTraceBridge

public section

namespace CFSG

namespace ZStar.PrincipalBlockTraceApplication

open ZStar.GroupAlgebraTwistedTrace
open ZStar.IntegralTraceBridge
open ZStar.PadicBlockField

noncomputable section

universe u v

variable {G : Type u} {R : Type v}

def coefficientTranslationMatrix [CommRing R] [Group G] [DecidableEq G] (x : G) :
    Matrix G G R :=
  (Equiv.mulRight x⁻¹).permMatrix R

private theorem rightMulMatrix_mul_coefficientTranslationMatrix_apply_self
    [CommRing R] [Group G] [Fintype G] [DecidableEq G]
    (a : MonoidAlgebra R G) (x g : G) :
    (rightMulMatrix a * coefficientTranslationMatrix (R := R) x) g g =
      a.coeff x := by
  change Matrix.vecMul (rightMulMatrix a g)
      ((Equiv.mulRight x⁻¹).permMatrix R) g = a.coeff x
  rw [Matrix.vecMul_permMatrix]
  simp [rightMulMatrix]

private theorem trace_rightMulMatrix_mul_coefficientTranslationMatrix
    [CommRing R] [Group G] [Fintype G] [DecidableEq G]
    (a : MonoidAlgebra R G) (x : G) :
    Matrix.trace
        (rightMulMatrix a * coefficientTranslationMatrix (R := R) x) =
      (Fintype.card G : R) * a.coeff x := by
  rw [Matrix.trace]
  simp_rw [Matrix.diag_apply]
  simp_rw [rightMulMatrix_mul_coefficientTranslationMatrix_apply_self a x]
  simp

theorem coeff_eq_iff_trace_rightMulMatrix_mul_coefficientTranslationMatrix_eq
    {K : Type v} [Field K] [CharZero K]
    [Group G] [Fintype G] [DecidableEq G]
    (a b : MonoidAlgebra K G) (x : G) :
    a.coeff x = b.coeff x ↔
      Matrix.trace
          (rightMulMatrix a * coefficientTranslationMatrix (R := K) x) =
        Matrix.trace
          (rightMulMatrix b * coefficientTranslationMatrix (R := K) x) := by
  rw [trace_rightMulMatrix_mul_coefficientTranslationMatrix,
    trace_rightMulMatrix_mul_coefficientTranslationMatrix]
  constructor
  · exact fun h ↦ congrArg ((Fintype.card G : K) * ·) h
  · intro h
    have hcardNat : Fintype.card G ≠ 0 := Fintype.card_ne_zero
    have hcard : (Fintype.card G : K) ≠ 0 := by
      exact_mod_cast hcardNat
    exact mul_left_cancel₀ hcard h

end

end ZStar.PrincipalBlockTraceApplication

end CFSG
