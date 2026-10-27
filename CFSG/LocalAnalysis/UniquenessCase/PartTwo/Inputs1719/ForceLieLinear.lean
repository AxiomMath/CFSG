module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.ForceLieTools
public import CFSG.GF2Type.Smith1979.CaseIIExclL52

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

open Matrix CFSG.Blueprint

private def gl6A : Matrix (Fin 6) (Fin 6) (ZMod 2) :=
  !![0, 1, 0, 0, 0, 0; 1, 1, 0, 0, 0, 0; 0, 0, 1, 0, 0, 0; 0, 0, 0, 1, 0, 0; 0, 0, 0, 0, 1, 0;
    0, 0, 0, 0, 0, 1]

private def gl6B : Matrix (Fin 6) (Fin 6) (ZMod 2) :=
  !![0, 0, 0, 0, 1, 0; 0, 0, 0, 0, 0, 1; 1, 0, 0, 0, 0, 0; 0, 1, 0, 0, 0, 0; 0, 0, 1, 0, 0, 0;
    0, 0, 0, 1, 0, 0]

private def gl6G : Matrix (Fin 6) (Fin 6) (ZMod 2) :=
  !![0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 0, 0; 0, 0, 1, 0, 0, 0; 0, 0, 0, 1, 0, 0; 0, 0, 0, 0, 1, 0;
    0, 0, 0, 0, 0, 1]

private def gl6K : Matrix (Fin 6) (Fin 6) (ZMod 2) :=
  !![1, 0, 0, 0, 0, 0; 0, 1, 0, 0, 0, 0; 0, 0, 0, 0, 1, 0; 0, 0, 0, 0, 0, 1; 0, 0, 1, 0, 0, 0;
    0, 0, 0, 1, 0, 0]

private theorem gl6_facts : gl6A * (gl6A * gl6A) = 1 ∧ gl6B * (gl6B * gl6B) = 1 ∧
    gl6G * gl6G = 1 ∧ gl6K * gl6K = 1 ∧
    gl6A * (gl6B * gl6A * (gl6B * gl6B)) = gl6B * gl6A * (gl6B * gl6B) * gl6A ∧
    gl6A * gl6B ≠ gl6B * gl6A ∧ gl6G * gl6A * gl6G = gl6A * gl6A ∧
    gl6K * gl6B * gl6K = gl6B * gl6B := by
  decide +kernel

theorem forceRealPair_gl6 : ForceRealPair (GL (Fin 6) (ZMod 2)) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := gl6_facts
  let a : GL (Fin 6) (ZMod 2) := ⟨gl6A, gl6A * gl6A, h1, by rw [mul_assoc]; exact h1⟩
  let b : GL (Fin 6) (ZMod 2) := ⟨gl6B, gl6B * gl6B, h2, by rw [mul_assoc]; exact h2⟩
  let g : GL (Fin 6) (ZMod 2) := ⟨gl6G, gl6G, h3, h3⟩
  let k : GL (Fin 6) (ZMod 2) := ⟨gl6K, gl6K, h4, h4⟩
  exact ⟨a, b, g, k, forceRealPair_facts_of_matrix a b g k (by rw [mul_assoc]; exact h1)
    (by rw [mul_assoc]; exact h2) h5 h6 h7 h8⟩

private def gl7A : Matrix (Fin 7) (Fin 7) (ZMod 2) :=
  !![0, 1, 0, 0, 0, 0, 0; 1, 1, 0, 0, 0, 0, 0; 0, 0, 1, 0, 0, 0, 0; 0, 0, 0, 1, 0, 0, 0;
    0, 0, 0, 0, 1, 0, 0; 0, 0, 0, 0, 0, 1, 0; 0, 0, 0, 0, 0, 0, 1]

private def gl7B : Matrix (Fin 7) (Fin 7) (ZMod 2) :=
  !![0, 0, 0, 0, 1, 0, 0; 0, 0, 0, 0, 0, 1, 0; 1, 0, 0, 0, 0, 0, 0; 0, 1, 0, 0, 0, 0, 0;
    0, 0, 1, 0, 0, 0, 0; 0, 0, 0, 1, 0, 0, 0; 0, 0, 0, 0, 0, 0, 1]

private def gl7G : Matrix (Fin 7) (Fin 7) (ZMod 2) :=
  !![0, 1, 0, 0, 0, 0, 0; 1, 0, 0, 0, 0, 0, 0; 0, 0, 1, 0, 0, 0, 0; 0, 0, 0, 1, 0, 0, 0;
    0, 0, 0, 0, 1, 0, 0; 0, 0, 0, 0, 0, 1, 0; 0, 0, 0, 0, 0, 0, 1]

private def gl7K : Matrix (Fin 7) (Fin 7) (ZMod 2) :=
  !![1, 0, 0, 0, 0, 0, 0; 0, 1, 0, 0, 0, 0, 0; 0, 0, 0, 0, 1, 0, 0; 0, 0, 0, 0, 0, 1, 0;
    0, 0, 1, 0, 0, 0, 0; 0, 0, 0, 1, 0, 0, 0; 0, 0, 0, 0, 0, 0, 1]

private theorem gl7_facts : gl7A * (gl7A * gl7A) = 1 ∧ gl7B * (gl7B * gl7B) = 1 ∧
    gl7G * gl7G = 1 ∧ gl7K * gl7K = 1 ∧
    gl7A * (gl7B * gl7A * (gl7B * gl7B)) = gl7B * gl7A * (gl7B * gl7B) * gl7A ∧
    gl7A * gl7B ≠ gl7B * gl7A ∧ gl7G * gl7A * gl7G = gl7A * gl7A ∧
    gl7K * gl7B * gl7K = gl7B * gl7B := by
  decide +kernel

theorem forceRealPair_gl7 : ForceRealPair (GL (Fin 7) (ZMod 2)) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := gl7_facts
  let a : GL (Fin 7) (ZMod 2) := ⟨gl7A, gl7A * gl7A, h1, by rw [mul_assoc]; exact h1⟩
  let b : GL (Fin 7) (ZMod 2) := ⟨gl7B, gl7B * gl7B, h2, by rw [mul_assoc]; exact h2⟩
  let g : GL (Fin 7) (ZMod 2) := ⟨gl7G, gl7G, h3, h3⟩
  let k : GL (Fin 7) (ZMod 2) := ⟨gl7K, gl7K, h4, h4⟩
  exact ⟨a, b, g, k, forceRealPair_facts_of_matrix a b g k (by rw [mul_assoc]; exact h1)
    (by rw [mul_assoc]; exact h2) h5 h6 h7 h8⟩

theorem forceRealPair_of_lieModel_PSL_six {Q : Type} [Group Q] (h : LieModel Q .PSL 6 2 1) :
    ForceRealPair Q := by
  obtain ⟨e⟩ := CFSG.GF2Type.Smith1979.Case2.nonempty_mulEquiv_gl_of_psl_two
    (h.statedClassicalModel_of_ne_zero (by norm_num))
  exact forceRealPair_gl6.of_mulEquiv e

theorem forceRealPair_of_lieModel_PSL_seven {Q : Type} [Group Q] (h : LieModel Q .PSL 7 2 1) :
    ForceRealPair Q := by
  obtain ⟨e⟩ := CFSG.GF2Type.Smith1979.Case2.nonempty_mulEquiv_gl_of_psl_two
    (h.statedClassicalModel_of_ne_zero (by norm_num))
  exact forceRealPair_gl7.of_mulEquiv e

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
