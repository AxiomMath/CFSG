module

public import CFSG.ClassicalInvolution.Balance.StrongPowSuBlocks
public import CFSG.ClassicalGroups.Unitary.SUThreeTwoDiagHom
public import CFSG.LocalAnalysis.StandardType.GGSecFivePhanNSPosDefs
import CFSG.LocalAnalysis.StandardType.GGQTwoDUnitBlock
public import CFSG.ClassicalInvolution.Balance.PassTwoFinal
public import CFSG.ClassicalInvolution.Models.LinearFrames
public import CFSG.ClassicalInvolution.Models.LinearPairs
public import CFSG.LieType.Ree.SmallReeModelSchreier
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOddLieClassical
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOddLieE6E7Triality

public section

set_option autoImplicit false

namespace CFSG.StandardType.QTwo

open CFSG.ClassicalInvolution.Balance.StrongBalance.Unitary CFSG.ClassicalInvolution.Phan
  CFSG.LieType.Steinberg CFSG.ClassicalGroups.Unitary.SUThreeTwoDiag Matrix
open CFSG.ClassicalInvolution.Balance.StrongBalance.Linear (blockOn blockOn_apply_mem
  blockOn_apply_not_mem)

variable {K : Type} [Field K] [Finite K] [CharP K 2] {n : ℕ}

theorem ggQTwoDUnit_coe_blockSUOn_dconjSu (hK : Nat.card K = 4) (J : Finset (Fin n))
    {g : GL (Fin n) K} {u : Fin n → Kˣ}
    (hgu : (g : Matrix (Fin n) (Fin n) K) = Matrix.diagonal fun i => (u i : K))
    (X : Su K 2 1 J.card) :
    ((blockSUOn K 2 1 J (dconjSu hK (fun k => u (J.equivFin.symm k)) X) : Su K 2 1 n) :
        GL (Fin n) K) = g * (blockSUOn K 2 1 J X : GL (Fin n) K) * g⁻¹ := by
  obtain rfl : g = diagGL u := Units.ext (hgu.trans (coe_diagGL u).symm)
  apply Units.ext
  rw [coe_coe_blockSUOn, coe_dconjSu, Units.val_mul, Units.val_mul, Units.val_mul, Units.val_mul,
    coe_diagGL, coe_diagGL_inv, coe_diagGL, coe_diagGL_inv, coe_coe_blockSUOn]
  ext i j
  rw [mul_diagonal, diagonal_mul]
  by_cases hi : i ∈ J
  · by_cases hj : j ∈ J
    · rw [blockOn_apply_mem J _ hi hj, blockOn_apply_mem J _ hi hj, mul_diagonal, diagonal_mul]
      simp
    · rw [blockOn_apply_not_mem J _ (Or.inr hj), blockOn_apply_not_mem J _ (Or.inr hj)]
      split_ifs with h
      · subst h
        simp
      · simp
  · rw [blockOn_apply_not_mem J _ (Or.inl hi), blockOn_apply_not_mem J _ (Or.inl hi)]
    split_ifs with h
    · subst h
      simp
    · simp

end CFSG.StandardType.QTwo

end
