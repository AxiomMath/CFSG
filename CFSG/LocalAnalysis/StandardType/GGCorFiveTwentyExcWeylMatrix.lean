module

public import CFSG.LieType.Chevalley.WeylRoots

public noncomputable section

namespace CFSG.StandardType

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley Matrix

variable {τ : Tag}

@[expose] def weylLatticeMatrix (τ : Tag) (w : WeylGroup τ) : Matrix (Fin τ.rank) (Fin τ.rank) ℤ :=
  Matrix.of fun i j => (w • (Pi.single j 1 : Fin τ.rank → ℤ)) i

theorem weylLatticeMatrix_apply (w : WeylGroup τ) (i j : Fin τ.rank) :
    weylLatticeMatrix τ w i j = (w • (Pi.single j 1 : Fin τ.rank → ℤ)) i :=
  rfl

theorem weylLatticeMatrix_mulVec (w : WeylGroup τ) (x : Fin τ.rank → ℤ) :
    weylLatticeMatrix τ w *ᵥ x = w • x := by
  conv_rhs => rw [← Finset.univ_sum_single x]
  rw [Finset.smul_sum]
  funext i
  simp only [mulVec, dotProduct, weylLatticeMatrix_apply, Finset.sum_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  have h : (Pi.single j (x j) : Fin τ.rank → ℤ) = x j • Pi.single j 1 := by
    rw [← Pi.single_smul, smul_eq_mul, mul_one]
  rw [h, smul_comm, Pi.smul_apply, smul_eq_mul, mul_comm]

theorem weylLatticeMatrix_mul (w w' : WeylGroup τ) :
    weylLatticeMatrix τ (w * w') = weylLatticeMatrix τ w * weylLatticeMatrix τ w' := by
  ext i j
  have h1 : weylLatticeMatrix τ (w * w') i j = (w • w' • (Pi.single j 1 : Fin τ.rank → ℤ)) i := by
    rw [weylLatticeMatrix_apply, mul_smul]
  have h2 : (weylLatticeMatrix τ w * weylLatticeMatrix τ w') i j =
      (weylLatticeMatrix τ w *ᵥ (w' • (Pi.single j 1 : Fin τ.rank → ℤ))) i := by
    simp only [Matrix.mul_apply, Matrix.mulVec, dotProduct, weylLatticeMatrix_apply w' _ j]
  rw [h1, h2, weylLatticeMatrix_mulVec]

theorem weylLatticeMatrix_one : weylLatticeMatrix τ (1 : WeylGroup τ) = 1 := by
  ext i j
  simp [weylLatticeMatrix_apply, Pi.single_apply, Matrix.one_apply]

theorem weylLatticeMatrix_mul_self {w : WeylGroup τ} (hw : w * w = 1) :
    weylLatticeMatrix τ w * weylLatticeMatrix τ w = 1 := by
  rw [← weylLatticeMatrix_mul, hw, weylLatticeMatrix_one]

end CFSG.StandardType

end
