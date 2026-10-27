module

public import CFSG.RankThree.PartOne.KF4.MinNative
public import CFSG.LieType.Chevalley.ToralCentralizerBruhat

public noncomputable section

namespace CFSG.RankThree.PartOne.KF4

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley Matrix
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open scoped Pointwise

namespace MinNativeData

variable {τ : Tag} {n : ℕ} {J : Set (Fin τ.rank)} {w : Fin n → Fin τ.rank → ℤ}
  (D : MinNativeData τ n J w) {K : Type} [Field K]

theorem rootDiagUnit_vec (b : Fin τ.rank → Kˣ) (k : Fin n) :
    ((rootDiagUnit τ b : ModGL τ K) : Module.End K (RootModule τ K)) (D.vec K k) =
      ((rootChar b (w k) : Kˣ) : K) • D.vec K k := by
  rw [← D.rootVec_w]
  exact rootDiag_rootVec b (D.isRoot k)

theorem rootDiagUnit_inv_vec (b : Fin τ.rank → Kˣ) (k : Fin n) :
    (((rootDiagUnit τ b)⁻¹ : ModGL τ K) : Module.End K (RootModule τ K)) (D.vec K k) =
      (((rootChar b (w k))⁻¹ : Kˣ) : K) • D.vec K k := by
  rw [← D.rootVec_w]
  exact rootDiagUnit_inv_rootVec b (D.isRoot k)

theorem Mat_conj_rootDiagUnit (b : Fin τ.rank → Kˣ) {g : ModGL τ K}
    (hg : g ∈ subsystemGroup τ K J) :
    D.Mat (rootDiagUnit τ b * g * (rootDiagUnit τ b)⁻¹) =
      Matrix.diagonal (fun k => ((rootChar b (w k) : Kˣ) : K)) * D.Mat g *
        Matrix.diagonal (fun k => (((rootChar b (w k))⁻¹ : Kˣ) : K)) := by
  have e : ∀ c : Fin n,
      ((rootDiagUnit τ b * g * (rootDiagUnit τ b)⁻¹ : ModGL τ K) :
        Module.End K (RootModule τ K)) (D.vec K c) =
      ∑ i, (((rootChar b (w i) : Kˣ) : K) * D.Mat g i c *
        (((rootChar b (w c))⁻¹ : Kˣ) : K)) • D.vec K i := by
    intro c
    rw [Units.val_mul, Units.val_mul, Module.End.mul_apply, Module.End.mul_apply,
      D.rootDiagUnit_inv_vec, map_smul, D.apply_vec hg, map_smul, map_sum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul, D.rootDiagUnit_vec, smul_smul, smul_smul]
    congr 1
    ring
  ext a c
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul, Mat, Matrix.of_apply, e, Finsupp.finsetSum_apply]
  simp only [Finsupp.smul_apply, D.vec_apply, smul_eq_mul, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq, Finset.mem_univ, ite_true]

end MinNativeData

end CFSG.RankThree.PartOne.KF4
