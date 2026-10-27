module

public import CFSG.Assembly.GL83LieDefs

public section

namespace CFSG.StandardType.FrameRoute.OmegaTen

open CFSG.Assembly
open scoped Matrix commutatorElement

abbrev Idx : Type := LargeEvenMinusIdx 4

abbrev ix (k : Fin 4) : Idx := Sum.inl (Sum.inl k)

abbrev iy (k : Fin 4) : Idx := Sum.inl (Sum.inr k)

abbrev iu : Idx := Sum.inr 0

abbrev iv : Idx := Sum.inr 1

abbrev quadTen : (Idx → ZMod 2) → ZMod 2 := LargeEvenQMinus 4 1 1

@[expose] def polar (x y : Idx → ZMod 2) : ZMod 2 :=
  (∑ k : Fin 4, (x (ix k) * y (iy k) + x (iy k) * y (ix k))) + x iu * y iv + x iv * y iu

theorem quadTen_add (x y : Idx → ZMod 2) :
    quadTen (x + y) = quadTen x + quadTen y + polar x y := by
  simp only [quadTen, polar, LargeEvenQMinus, Pi.add_apply, Fin.sum_univ_four]
  ring_nf
  linear_combination (x iu * y iu + x iv * y iv) * CharTwo.two_eq_zero (R := ZMod 2)

theorem polar_self (x : Idx → ZMod 2) : polar x x = 0 := by
  simp only [polar, Fin.sum_univ_four]
  ring_nf
  linear_combination (x iu * x iv + x (ix 0) * x (iy 0) + x (ix 1) * x (iy 1) +
    x (ix 2) * x (iy 2) + x (ix 3) * x (iy 3)) * CharTwo.two_eq_zero (R := ZMod 2)

@[expose] def reflMat (n : Idx → ZMod 2) : Matrix Idx Idx (ZMod 2) :=
  1 + Matrix.of fun i j => n i * polar (Pi.single j 1) n

private theorem omegaTenRefl_polar_sum (x n : Idx → ZMod 2) :
    (∑ j, x j * polar (Pi.single j 1) n) = polar x n := by
  simp [polar, Fin.sum_univ_four, Fintype.sum_sum_type, Pi.single_apply]
  ring

private theorem omegaTenRefl_sum_mul (n x : Idx → ZMod 2) (i : Idx) :
    (∑ j, n i * polar (Pi.single j 1) n * x j) = n i * polar x n := by
  rw [← omegaTenRefl_polar_sum x n, Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => by ring

theorem reflMat_mulVec (n x : Idx → ZMod 2) : reflMat n *ᵥ x = x + polar x n • n := by
  funext i
  rw [reflMat, Matrix.add_mulVec, Matrix.one_mulVec]
  simp only [Matrix.mulVec, dotProduct, Matrix.of_apply, Pi.add_apply, Pi.smul_apply,
    omegaTenRefl_sum_mul]
  ring

private theorem omegaTenRefl_polar_add (x y n : Idx → ZMod 2) :
    polar (x + y) n = polar x n + polar y n := by
  simp only [polar, Pi.add_apply, Fin.sum_univ_four]
  ring

private theorem omegaTenRefl_polar_smul (c : ZMod 2) (x n : Idx → ZMod 2) :
    polar (c • x) n = c * polar x n := by
  simp only [polar, Pi.smul_apply, Fin.sum_univ_four, smul_eq_mul]
  ring

private theorem omegaTenRefl_polar_smul_right (x : Idx → ZMod 2) (c : ZMod 2)
    (n : Idx → ZMod 2) : polar x (c • n) = c * polar x n := by
  simp only [polar, Pi.smul_apply, Fin.sum_univ_four, smul_eq_mul]
  ring

private theorem omegaTenRefl_quadTen_smul (c : ZMod 2) (x : Idx → ZMod 2) :
    quadTen (c • x) = c ^ 2 * quadTen x := by
  simp only [quadTen, LargeEvenQMinus, Pi.smul_apply, Fin.sum_univ_four, smul_eq_mul]
  ring

theorem reflMat_mul_self (n : Idx → ZMod 2) : reflMat n * reflMat n = 1 := by
  refine Matrix.mulVec_injective (n := Idx) ?_
  funext x
  rw [← Matrix.mulVec_mulVec, Matrix.one_mulVec]
  rw [reflMat_mulVec n (reflMat n *ᵥ x)]
  rw [reflMat_mulVec n x]
  rw [omegaTenRefl_polar_add, omegaTenRefl_polar_smul, polar_self, mul_zero, add_zero]
  funext i
  simp only [Pi.add_apply, Pi.smul_apply]
  linear_combination (n i * polar x n) * CharTwo.two_eq_zero (R := ZMod 2)

theorem quadTen_reflMat_mulVec {n : Idx → ZMod 2} (hn : quadTen n = 1) (x : Idx → ZMod 2) :
    quadTen (reflMat n *ᵥ x) = quadTen x := by
  rw [reflMat_mulVec, quadTen_add, omegaTenRefl_quadTen_smul, omegaTenRefl_polar_smul_right,
    hn]
  ring_nf
  linear_combination (polar x n ^ 2) * CharTwo.two_eq_zero (R := ZMod 2)

@[expose] def reflGL (n : Idx → ZMod 2) : GL Idx (ZMod 2) :=
  ⟨reflMat n, reflMat n, reflMat_mul_self n, reflMat_mul_self n⟩

theorem reflGL_mem_largeEvenOrthGroup {n : Idx → ZMod 2} (hn : quadTen n = 1) :
    reflGL n ∈ LargeEvenOrthGroup quadTen := by
  rw [largeEvenOrthGroup_def]
  exact Subgroup.subset_closure fun x => quadTen_reflMat_mulVec hn x

theorem commutator_reflGL_mem {m n : Idx → ZMod 2} (hm : quadTen m = 1) (hn : quadTen n = 1) :
    ⁅reflGL m, reflGL n⁆ ∈ LargeEvenOmega quadTen := by
  rw [largeEvenOmega_def]
  exact Subgroup.commutator_mem_commutator (reflGL_mem_largeEvenOrthGroup hm)
    (reflGL_mem_largeEvenOrthGroup hn)

end CFSG.StandardType.FrameRoute.OmegaTen

end
