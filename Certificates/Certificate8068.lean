module

public import CFSG.Quasithin.Background.Sp4InfConcInputs

public section

open CFSG CFSG.Quasithin CFSG.Quasithin.Sp4Inf CFSG.Assembly.LowTwoRank CFSG.Quasithin.H Matrix

namespace Certificates

open CFSG CFSG.Quasithin CFSG.Quasithin.Sp4Inf CFSG.Assembly.LowTwoRank CFSG.Quasithin.H Matrix in
theorem certificate8068 : ∀ M : Matrix I4 I4 (ZMod 2), M * aM = aM * M → M * bM = bM * M →
    M = 0 ∨ M = 1 := by
  intro M ha hb
  have e : ∀ i j, (M * aM) i j = (aM * M) i j := fun i j => by rw [ha]
  have f : ∀ i j, (M * bM) i j = (bM * M) i j := fun i j => by rw [hb]
  simp only [Matrix.mul_apply, Fintype.sum_sum_type, Fin.sum_univ_two, aM, bM, mk4,
    Matrix.of_apply, idx4, Sum.forall, Fin.forall_fin_two] at e f
  simp at e f
  have key : ∀ i j, M i j = if i = j then M (.inl 0) (.inl 0) else 0 := by
    intro i j
    rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j <;> simp <;> grind
  have h2 : ∀ x : ZMod 2, x = 0 ∨ x = 1 := by decide
  rcases h2 (M (.inl 0) (.inl 0)) with h | h
  · left
    ext i j
    rw [key, h]
    simp
  · right
    ext i j
    rw [key, h, Matrix.one_apply]

end Certificates
