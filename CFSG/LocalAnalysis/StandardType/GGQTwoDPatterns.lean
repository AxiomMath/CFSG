module

public import CFSG.LocalAnalysis.StandardType.GGCoxeterLabelCLLDType
public import Mathlib.GroupTheory.Coxeter.Basic

public section

namespace CFSG.StandardType.QTwo

@[expose] def QTwoPattern (m : ℕ) (T : Finset (Fin m)) : Prop :=
  (∃ i j, i ≠ j ∧ T = {i, j}) ∨
  (∃ i j k, ggCoxeterMatrixD m i j = 3 ∧ ggCoxeterMatrixD m j k = 3 ∧
      ggCoxeterMatrixD m i k = 2 ∧ T = {i, j, k}) ∨
  (∃ i j k, ggCoxeterMatrixD m j k = 3 ∧ ggCoxeterMatrixD m i j = 2 ∧
      ggCoxeterMatrixD m i k = 2 ∧ T = {i, j, k}) ∨
  (∃ i k j l, ggCoxeterMatrixD m i k = 3 ∧ ggCoxeterMatrixD m j l = 3 ∧
      ggCoxeterMatrixD m i j = 2 ∧ ggCoxeterMatrixD m i l = 2 ∧ ggCoxeterMatrixD m k j = 2 ∧
      ggCoxeterMatrixD m k l = 2 ∧ T = {i, k, j, l})

@[expose] def qtwoParabRefl (m : ℕ) : Set (ggCoxeterMatrixD m).Group :=
  {r | ∃ i : Fin m, (i : ℕ) ≠ 0 ∧ ∃ u ∈ Subgroup.closure
      ((ggCoxeterMatrixD m).simple '' {j : Fin m | (j : ℕ) ≠ 0}),
      r = u * (ggCoxeterMatrixD m).simple i * u⁻¹}

@[expose] def QTwoParabConj : Prop :=
  ∀ (m : ℕ), 7 ≤ m → ∀ (T : Finset (Fin m)), QTwoPattern m T →
    ∃ w : (ggCoxeterMatrixD m).Group, ∀ t ∈ T,
      w * (ggCoxeterMatrixD m).simple t * w⁻¹ ∈ qtwoParabRefl m

theorem simple_mem_qtwoParabRefl {m : ℕ} {i : Fin m} (hi : (i : ℕ) ≠ 0) :
    (ggCoxeterMatrixD m).simple i ∈ qtwoParabRefl m :=
  ⟨i, hi, 1, one_mem _, by simp⟩

end CFSG.StandardType.QTwo

end
