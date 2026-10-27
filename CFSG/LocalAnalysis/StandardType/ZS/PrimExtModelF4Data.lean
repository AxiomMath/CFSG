module

public import CFSG.LocalAnalysis.StandardType.ZS.PrimExtModelTable

public section

namespace CFSG.StandardType.ZS.PrimModel

@[expose] def f45RootL : List (List ℤ) := [
    [2, 0, 0, 0, 0],
    [0, 2, 0, 0, 0],
    [1, (-1), (-1), (-1), 0],
    [0, 0, 2, 0, 0],
    [(-1), 1, (-1), (-1), 0],
    [(-1), (-1), (-1), (-1), 0],
    [(-1), (-1), 1, (-1), 0],
    [1, 1, (-1), (-1), 0],
    [1, (-1), 1, (-1), 0],
    [(-1), 1, 1, (-1), 0],
    [1, 1, 1, (-1), 0],
    [0, 0, 0, (-2), 0],
    [1, (-1), 0, 0, 0],
    [(-1), (-1), 0, 0, 0],
    [1, 0, (-1), 0, 0],
    [(-1), 0, (-1), 0, 0],
    [0, 0, 1, 1, 0],
    [0, 1, (-1), 0, 0],
    [0, (-1), (-1), 0, 0],
    [0, 1, 0, 1, 0],
    [1, 0, 0, 1, 0],
    [(-1), 0, 0, 1, 0],
    [0, (-1), 0, 1, 0],
    [0, 0, (-1), 1, 0]]

@[expose] def f45CorootL : List (List ℤ) := [
    [2, 0, 0, 0, 0],
    [0, 2, 0, 0, 0],
    [1, (-1), (-1), (-1), 0],
    [0, 0, 2, 0, 0],
    [(-1), 1, (-1), (-1), 0],
    [(-1), (-1), (-1), (-1), 0],
    [(-1), (-1), 1, (-1), 0],
    [1, 1, (-1), (-1), 0],
    [1, (-1), 1, (-1), 0],
    [(-1), 1, 1, (-1), 0],
    [1, 1, 1, (-1), 0],
    [0, 0, 0, (-2), 0],
    [2, (-2), 0, 0, 0],
    [(-2), (-2), 0, 0, 0],
    [2, 0, (-2), 0, 0],
    [(-2), 0, (-2), 0, 0],
    [0, 0, 2, 2, 0],
    [0, 2, (-2), 0, 0],
    [0, (-2), (-2), 0, 0],
    [0, 2, 0, 2, 0],
    [2, 0, 0, 2, 0],
    [(-2), 0, 0, 2, 0],
    [0, (-2), 0, 2, 0],
    [0, 0, (-2), 2, 0]]

@[expose] def f45ConjL : List (List (Fin 24)) := [
    [0, 1, 5, 3, 7, 2, 8, 4, 6, 10, 9, 11, 13, 12, 15, 14, 16, 17, 18, 19, 21, 20, 22, 23],
    [1, 0, 4, 3, 2, 5, 6, 7, 9, 8, 10, 11, 12, 13, 17, 18, 16, 14, 15, 20, 19, 22, 21, 23],
    [0, 3, 2, 1, 6, 5, 4, 8, 7, 9, 10, 11, 14, 15, 12, 13, 19, 17, 18, 16, 20, 21, 23, 22],
    [2, 4, 0, 6, 1, 5, 3, 7, 8, 9, 11, 10, 12, 16, 14, 19, 13, 17, 20, 15, 18, 21, 22, 23]]

@[expose] def f45SignL : List (List Bool) := [
    [false, true, true, true, true, true, true, true, true, true, true, true, true, true, true,
    true, true, true, true, true, true, true, true, true],
    [true, true, true, true, true, true, true, true, true, true, true, true, false, true, true,
    true, true, true, true, true, true, true, true, true],
    [true, true, true, true, true, true, true, true, true, true, true, true, true, true, true,
    true, true, false, true, true, true, true, true, true],
    [true, true, true, true, true, false, true, true, true, true, true, true, true, true, true,
    true, true, true, true, true, true, true, true, true]]

@[expose] def f45WordL : List (List (Fin 4)) := [
    [],
    [1],
    [3],
    [2, 1],
    [3, 1],
    [0, 3],
    [3, 2, 1],
    [0, 3, 1],
    [0, 3, 2, 1],
    [1, 0, 3, 2, 1],
    [0, 1, 0, 3, 2, 1],
    [3, 0, 1, 0, 3, 2, 1],
    [],
    [0],
    [2],
    [2, 0],
    [3, 0],
    [1, 2],
    [1, 2, 0],
    [3, 2, 0],
    [3, 1, 2, 0],
    [0, 3, 1, 2, 0],
    [1, 0, 3, 1, 2, 0],
    [2, 1, 0, 3, 1, 2, 0]]

@[expose] def f45ClsL : List (Fin 4) :=
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]

@[expose] def f45GenL : List (Fin 24) := [0, 12, 17, 5]

@[expose] def f45Tab : ReflTable ℤ 5 4 24 where
  root j i := (f45RootL.getD j []).getD i 0
  coroot j i := (f45CorootL.getD j []).getD i 0
  gen k := f45GenL.getD k 0
  conj k j := (f45ConjL.getD k []).getD j 0
  sign k j := (f45SignL.getD k []).getD j true
  word j := f45WordL.getD j []
  cls j := f45ClsL.getD j 0

@[expose] def f45G : Fin 4 → Matrix (Fin 5) (Fin 5) ℤ := ![
    !![(-2), 0, 0, 0, 0; 0, 2, 0, 0, 0; 0, 0, 2, 0, 0; 0, 0, 0, 2, 0; 0, 0, 0, 0, 2],
    !![0, 2, 0, 0, 0; 2, 0, 0, 0, 0; 0, 0, 2, 0, 0; 0, 0, 0, 2, 0; 0, 0, 0, 0, 2],
    !![2, 0, 0, 0, 0; 0, 0, 2, 0, 0; 0, 2, 0, 0, 0; 0, 0, 0, 2, 0; 0, 0, 0, 0, 2],
    !![1, (-1), (-1), (-1), 0; (-1), 1, (-1), (-1), 0; (-1), (-1), 1, (-1), 0; (-1), (-1), (-1),
    1, 0; 0, 0, 0, 0, 2]]

@[expose] def f45WitL : List (Fin 24) :=
    [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 3, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0]

@[expose] def f45Wit (j : Fin 24) : Fin 24 := f45WitL.getD j 0

@[expose] def f44RootL : List (List ℤ) := [
    [(-1), (-1), (-1), (-1)],
    [1, (-1), (-1), (-1)],
    [2, 0, 0, 0],
    [(-1), 1, (-1), (-1)],
    [0, 2, 0, 0],
    [1, 1, (-1), (-1)],
    [(-1), (-1), 1, (-1)],
    [0, 0, 2, 0],
    [1, (-1), 1, (-1)],
    [(-1), 1, 1, (-1)],
    [1, 1, 1, (-1)],
    [0, 0, 0, (-2)],
    [(-1), 1, 0, 0],
    [1, 1, 0, 0],
    [(-1), 0, 1, 0],
    [0, 0, (-1), (-1)],
    [1, 0, 1, 0],
    [0, (-1), 1, 0],
    [0, (-1), 0, (-1)],
    [0, 1, 1, 0],
    [(-1), 0, 0, (-1)],
    [1, 0, 0, (-1)],
    [0, 1, 0, (-1)],
    [0, 0, 1, (-1)]]

@[expose] def f44CorootL : List (List ℤ) := [
    [(-1), (-1), (-1), (-1)],
    [1, (-1), (-1), (-1)],
    [2, 0, 0, 0],
    [(-1), 1, (-1), (-1)],
    [0, 2, 0, 0],
    [1, 1, (-1), (-1)],
    [(-1), (-1), 1, (-1)],
    [0, 0, 2, 0],
    [1, (-1), 1, (-1)],
    [(-1), 1, 1, (-1)],
    [1, 1, 1, (-1)],
    [0, 0, 0, (-2)],
    [(-2), 2, 0, 0],
    [2, 2, 0, 0],
    [(-2), 0, 2, 0],
    [0, 0, (-2), (-2)],
    [2, 0, 2, 0],
    [0, (-2), 2, 0],
    [0, (-2), 0, (-2)],
    [0, 2, 2, 0],
    [(-2), 0, 0, (-2)],
    [2, 0, 0, (-2)],
    [0, 2, 0, (-2)],
    [0, 0, 2, (-2)]]

@[expose] def f44ConjL : List (List (Fin 24)) := [
    [0, 2, 1, 4, 3, 5, 7, 6, 8, 9, 11, 10, 12, 15, 14, 13, 18, 17, 16, 20, 19, 21, 22, 23],
    [1, 0, 2, 5, 4, 3, 8, 7, 6, 10, 9, 11, 13, 12, 16, 15, 14, 17, 18, 19, 21, 20, 22, 23],
    [0, 3, 4, 1, 2, 5, 6, 7, 9, 8, 10, 11, 12, 13, 17, 15, 19, 14, 20, 16, 18, 22, 21, 23],
    [0, 1, 2, 6, 7, 8, 3, 4, 5, 9, 10, 11, 14, 16, 12, 18, 13, 17, 15, 19, 20, 21, 23, 22]]

@[expose] def f44SignL : List (List Bool) := [
    [false, true, true, true, true, true, true, true, true, true, true, true, true, true, true,
    true, true, true, true, true, true, true, true, true],
    [true, true, false, true, true, true, true, true, true, true, true, true, true, true, true,
    true, true, true, true, true, true, true, true, true],
    [true, true, true, true, true, true, true, true, true, true, true, true, false, true, true,
    true, true, true, true, true, true, true, true, true],
    [true, true, true, true, true, true, true, true, true, true, true, true, true, true, true,
    true, true, false, true, true, true, true, true, true]]

@[expose] def f44WordL : List (List (Fin 4)) := [
    [],
    [1],
    [0, 1],
    [2, 1],
    [2, 0, 1],
    [1, 2, 1],
    [3, 2, 1],
    [3, 2, 0, 1],
    [3, 1, 2, 1],
    [2, 3, 1, 2, 1],
    [1, 2, 3, 1, 2, 1],
    [0, 1, 2, 3, 1, 2, 1],
    [],
    [1],
    [3],
    [0, 1],
    [3, 1],
    [2, 3],
    [3, 0, 1],
    [2, 3, 1],
    [2, 3, 0, 1],
    [1, 2, 3, 0, 1],
    [2, 1, 2, 3, 0, 1],
    [3, 2, 1, 2, 3, 0, 1]]

@[expose] def f44ClsL : List (Fin 4) :=
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]

@[expose] def f44GenL : List (Fin 24) := [0, 2, 12, 17]

@[expose] def f44Tab : ReflTable ℤ 4 4 24 where
  root j i := (f44RootL.getD j []).getD i 0
  coroot j i := (f44CorootL.getD j []).getD i 0
  gen k := f44GenL.getD k 0
  conj k j := (f44ConjL.getD k []).getD j 0
  sign k j := (f44SignL.getD k []).getD j true
  word j := f44WordL.getD j []
  cls j := f44ClsL.getD j 0

@[expose] def f44G : Fin 4 → Matrix (Fin 4) (Fin 4) ℤ := ![
    !![1, (-1), (-1), (-1); (-1), 1, (-1), (-1); (-1), (-1), 1, (-1); (-1), (-1), (-1), 1],
    !![(-2), 0, 0, 0; 0, 2, 0, 0; 0, 0, 2, 0; 0, 0, 0, 2],
    !![0, 2, 0, 0; 2, 0, 0, 0; 0, 0, 2, 0; 0, 0, 0, 2],
    !![2, 0, 0, 0; 0, 0, 2, 0; 0, 2, 0, 0; 0, 0, 0, 2]]

@[expose] def f44SpanL : List (List ℤ) := [
    [0, 1, 0, 0],
    [0, 1, 2, 0],
    [0, 1, 2, 2],
    [-2, -3, -4, -2]]

@[expose] def f44Span (l i : Fin 4) : ℤ := (f44SpanL.getD l []).getD i 0

@[expose] def f45D : Fin 5 → ℤ := fun _ => 1

@[expose] def f44Cartan : Matrix (Fin 4) (Fin 4) ℤ :=
  !![2, -1, 0, 0; -1, 2, -2, 0; 0, -1, 2, -1; 0, 0, -1, 2]

theorem f45Tab_valid : f45Tab.Valid GoodZ :=
  ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel⟩

theorem f45Tab_gen : ∀ k : Fin 4,
    reflZ (f45Tab.root (f45Tab.gen k)) (f45Tab.coroot (f45Tab.gen k)) = f45G k := by
  decide +kernel

theorem f45Tab_form : ∀ k : Fin 4,
    (∑ i, f45D i * f45Tab.root (f45Tab.gen k) i ^ 2) • f45Tab.coroot (f45Tab.gen k) =
      (4 : ℤ) • fun i => f45D i * f45Tab.root (f45Tab.gen k) i := by
  decide +kernel

theorem f45D_good : ∀ i, GoodZ (f45D i) := by
  decide +kernel

theorem f45Tab_wit : ∀ j, (∀ i ∉ ({0, 1, 2} : Finset (Fin 5)), f45Tab.root j i = 0) →
    (∀ i ∉ ({0, 1, 2} : Finset (Fin 5)), f45Tab.root (f45Wit j) i = 0) ∧
      dotProduct (f45Tab.coroot j) (f45Tab.root (f45Wit j)) = 0 ∧
      f45Tab.cls (f45Wit j) = f45Tab.cls 0 := by
  decide +kernel

theorem f45Tab_diag : reflZ (f45Tab.root 0) (f45Tab.coroot 0) = diagZ 0 ∧
    reflZ (f45Tab.root 1) (f45Tab.coroot 1) = diagZ 1 ∧
    reflZ (f45Tab.root 3) (f45Tab.coroot 3) = diagZ 2 ∧
    reflZ (f45Tab.root 11) (f45Tab.coroot 11) = diagZ 3 := by
  decide +kernel

theorem f44Tab_valid : f44Tab.Valid GoodZ :=
  ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel⟩

theorem f44Tab_gen : ∀ k : Fin 4,
    reflZ (f44Tab.root (f44Tab.gen k)) (f44Tab.coroot (f44Tab.gen k)) = f44G k := by
  decide +kernel

theorem f44_cartan : ∀ i j : Fin 4,
    dotProduct (f44Tab.coroot (f44Tab.gen j)) (f44Tab.root (f44Tab.gen i)) = 2 * f44Cartan i j := by
  decide +kernel

theorem f44_span : ∀ l : Fin 4,
    ∑ i, f44Span l i • f44Tab.root (f44Tab.gen i) = (2 : ℤ) ^ 1 • Pi.single l 1 := by
  decide +kernel

end CFSG.StandardType.ZS.PrimModel

end
