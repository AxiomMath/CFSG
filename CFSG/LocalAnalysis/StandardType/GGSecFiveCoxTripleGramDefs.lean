module

public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

public section

namespace CFSG.StandardType.CoxTriple

@[expose] def gramRefl (N : Matrix (Fin 3) (Fin 3) ℤ) (k : Fin 3) : Matrix (Fin 3) (Fin 3) ℤ :=
  1 - Matrix.of fun i j => if i = k then 2 * N k j / N k k else 0

@[expose] def gramReflGroup (N : Matrix (Fin 3) (Fin 3) ℤ) : Submonoid (Matrix (Fin 3) (Fin 3) ℤ) :=
  Submonoid.closure (Set.range (gramRefl N))

@[expose] def AdmGram (N : Matrix (Fin 3) (Fin 3) ℤ) : Prop :=
  (∀ k l : Fin 3, N k l = N l k) ∧ (N 0 0 = 2 ∨ N 0 0 = 4) ∧ N 1 1 = N 0 0 ∧ (N 2 2 = 2 ∨ N 2 2 = 4) ∧ 2 * N 0 1 = -N 0 0 ∧
    (∀ k l : Fin 3, N k k ∣ 2 * N k l) ∧
    (∀ k l : Fin 3, k ≠ l →
      (2 * N k l / N k k) * (2 * N k l / N l l) = 0 ∨ (2 * N k l / N k k) * (2 * N k l / N l l) = 1 ∨
        (2 * N k l / N k k) * (2 * N k l / N l l) = 2) ∧
    0 < N 0 0 * N 1 1 - N 0 1 ^ 2 ∧ 0 < N 0 0 * N 2 2 - N 0 2 ^ 2 ∧ 0 < N 1 1 * N 2 2 - N 1 2 ^ 2 ∧
    0 < N.det

@[expose] def admList : List (Matrix (Fin 3) (Fin 3) ℤ) := [
  !![2, -1, -1; -1, 2, 0; -1, 0, 2],
  !![2, -1, -1; -1, 2, 1; -1, 1, 2],
  !![2, -1, 0; -1, 2, -1; 0, -1, 2],
  !![2, -1, 0; -1, 2, 0; 0, 0, 2],
  !![2, -1, 0; -1, 2, 1; 0, 1, 2],
  !![2, -1, 1; -1, 2, -1; 1, -1, 2],
  !![2, -1, 1; -1, 2, 0; 1, 0, 2],
  !![2, -1, -2; -1, 2, 0; -2, 0, 4],
  !![2, -1, -2; -1, 2, 2; -2, 2, 4],
  !![2, -1, 0; -1, 2, -2; 0, -2, 4],
  !![2, -1, 0; -1, 2, 0; 0, 0, 4],
  !![2, -1, 0; -1, 2, 2; 0, 2, 4],
  !![2, -1, 2; -1, 2, -2; 2, -2, 4],
  !![2, -1, 2; -1, 2, 0; 2, 0, 4],
  !![4, -2, -2; -2, 4, 0; -2, 0, 2],
  !![4, -2, -2; -2, 4, 2; -2, 2, 2],
  !![4, -2, 0; -2, 4, -2; 0, -2, 2],
  !![4, -2, 0; -2, 4, 0; 0, 0, 2],
  !![4, -2, 0; -2, 4, 2; 0, 2, 2],
  !![4, -2, 2; -2, 4, -2; 2, -2, 2],
  !![4, -2, 2; -2, 4, 0; 2, 0, 2],
  !![4, -2, -2; -2, 4, 0; -2, 0, 4],
  !![4, -2, -2; -2, 4, 2; -2, 2, 4],
  !![4, -2, 0; -2, 4, -2; 0, -2, 4],
  !![4, -2, 0; -2, 4, 0; 0, 0, 4],
  !![4, -2, 0; -2, 4, 2; 0, 2, 4],
  !![4, -2, 2; -2, 4, -2; 2, -2, 4],
  !![4, -2, 2; -2, 4, 0; 2, 0, 4],
]

end CFSG.StandardType.CoxTriple

end
