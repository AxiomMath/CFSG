module

public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyExcWeylMatrix
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyExcReflectionCharpoly
public import CFSG.LieType.Chevalley.WeylSpace

public noncomputable section

namespace CFSG.StandardType

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley Matrix Polynomial Module

variable {τ : Tag}

theorem toMatrix_weylLinear (w : WeylGroup τ) :
    LinearMap.toMatrix (RootSpace.basis τ) (RootSpace.basis τ) (weylLinear τ w) =
      (weylLatticeMatrix τ w).map (Int.castRingHom ℝ) := by
  ext i j
  rw [LinearMap.toMatrix_apply, Matrix.map_apply, weylLatticeMatrix_apply, RootSpace.basis_apply,
    weylLinear_ofLattice, RootSpace.basis, Module.Basis.map_repr, LinearEquiv.trans_apply]
  simp

theorem weylLinear_comp_self {w : WeylGroup τ} (hw : w * w = 1) :
    weylLinear τ w ∘ₗ weylLinear τ w = LinearMap.id := by
  rw [← Module.End.mul_eq_comp, ← map_mul, hw, map_one, Module.End.one_eq_id]

theorem charpoly_weylLinear (w : WeylGroup τ) :
    (weylLinear τ w).charpoly = (weylLatticeMatrix τ w).charpoly.map (Int.castRingHom ℝ) := by
  rw [← LinearMap.charpoly_toMatrix (weylLinear τ w) (RootSpace.basis τ), toMatrix_weylLinear,
    Matrix.charpoly_map]

theorem finrank_ker_weylLinear_add_one {w : WeylGroup τ} (hw : w * w = 1) {k : ℕ}
    (hch : (weylLatticeMatrix τ w).charpoly = (X - 1) ^ k * (X + 1)) :
    finrank ℝ (LinearMap.ker (weylLinear τ w + 1)) = 1 := by
  have hchar := charpoly_involution (two_ne_zero : (2 : ℝ) ≠ 0) (weylLinear τ w)
    (weylLinear_comp_self hw)
  rw [charpoly_weylLinear w, hch] at hchar
  have hpoly : (X - 1 : ℝ[X]) ^ finrank ℝ (LinearMap.ker (weylLinear τ w - 1)) *
        (X + 1) ^ finrank ℝ (LinearMap.ker (weylLinear τ w + 1)) =
      (X - 1 : ℝ[X]) ^ k * (X + 1) ^ 1 := by
    simpa only [Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_sub, Polynomial.map_add,
      Polynomial.map_X, Polynomial.map_one, map_natCast, pow_one] using hchar.symm
  exact (pow_mul_pow_eq_iff (two_ne_zero : (2 : ℝ) ≠ 0) hpoly).2

end CFSG.StandardType

end
