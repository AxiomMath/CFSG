module

public import CFSG.LocalAnalysis.StandardType.GGCoxeterLabelAut
public import TauCeti.LinearAlgebra.IntegralLattice.RootLattice.TypeD.SimpleRoots

public section

namespace CFSG.StandardType

@[expose] def ggDForkPar (k : ℕ) (i : Fin k) : Fin k :=
  if i.1 + 1 = k then ⟨k - 3, by have := i.2; omega⟩ else ⟨i.1 - 1, by have := i.2; omega⟩

theorem ggCartanD_forkTree {k : ℕ} (hk : 4 ≤ k) (root : Fin k) (hroot : root.1 = 0) :
    (∀ i j, ggCoxeterMatrixD k i j ≠ 6) ∧
      (∀ i j : Fin k, i ≠ j → (CartanMatrix.D k i j ≠ 0 ↔
        ((i ≠ root ∧ ggDForkPar k i = j) ∨ (j ≠ root ∧ ggDForkPar k j = i)))) ∧
      (∀ i : Fin k, i ≠ root → (ggDForkPar k i).1 < i.1) := by
  have hval : ∀ i : Fin k, (ggDForkPar k i).1 = if i.1 + 1 = k then k - 3 else i.1 - 1 := by
    intro i
    unfold ggDForkPar
    split_ifs <;> rfl
  refine ⟨fun i j => ?_, fun i j hij => ?_, fun i hi => ?_⟩
  · rw [ggCoxeterMatrixD_apply]
    split_ifs <;> omega
  · have hij' : i.1 ≠ j.1 := fun h => hij (Fin.ext h)
    have hi := i.2
    have hj := j.2
    simp only [CartanMatrix.D, Matrix.of_apply, Fin.ext_iff, hval, hroot]
    split_ifs <;> omega
  · have hi' : i.1 ≠ 0 := fun h => hi (Fin.ext (h.trans hroot.symm))
    have hi2 := i.2
    rw [hval]
    split_ifs <;> omega

theorem ggCartanD_det_ne_zero {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {k : ℕ} (hk : 2 ≤ k) :
    (((CartanMatrix.D k).det : ℤ) : ZMod p) ≠ 0 := by
  rw [CartanMatrix.D_det hk]
  have h4 : ((4 : ℤ) : ZMod p) = 2 * 2 := by norm_num
  rw [h4]
  exact mul_ne_zero (zmod_two_ne_zero hp2) (zmod_two_ne_zero hp2)

end CFSG.StandardType

end
