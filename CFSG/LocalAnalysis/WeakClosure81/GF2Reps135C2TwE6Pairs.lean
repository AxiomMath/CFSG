module

public import CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisTw.F4Orbits
public import CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisTw.Weyl

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Blueprint.Chevalley CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisTw

@[expose] def tw2e6InnerWord : Fin 3 → List (Fin 4) :=
  ![[2], [0], [0, 3]]

@[expose] def tw2e6InnerPairs : Fin 3 → Fin 4 → List (List (Fin 4)) :=
  ![![[[1, 0], [3, 1, 2, 1, 0], [3, 0, 1, 2, 1, 0], [1, 2, 3, 0, 1, 2, 1, 0]],
      [[1], [0, 1], [1, 2, 0, 1], [3, 1, 2, 1]],
      [[], [1, 2], [0, 1, 2], [3, 1, 2]],
      [[3], [1, 2, 3], [0, 1, 2, 3], [1, 2, 0, 1, 2, 3]]],
    ![[[], [1, 2, 1, 0], [3, 1, 2, 1, 0], [2, 3, 1, 2, 1, 0]],
      [[1], [2, 1], [1, 2, 1], [3, 2, 1]],
      [[1, 2], [2, 1, 2], [3, 1, 2], [2, 3, 1, 2]],
      [[1, 2, 3], [2, 1, 2, 3], [3, 2, 1, 2, 3], [1, 2, 3, 1, 2, 0, 1, 2, 3]]],
    ![[[], [2, 1, 0], [1, 2, 1, 0], [0, 1, 2, 1, 0]],
      [[1], [2, 1], [1, 2, 1], [2, 0, 1]],
      [[2], [1, 2], [0, 1, 2], [2, 1, 2]],
      [[], [1, 2, 3], [2, 1, 2, 3], [2, 0, 1, 2, 3]]]]

@[expose] def tw2e6OuterPairs : Fin 4 → List (List (Fin 4)) :=
  ![[[], [1, 2, 1, 0], [3, 1, 2, 1, 0], [2, 3, 1, 2, 1, 0], [1, 2, 3, 1, 2, 1, 0],
      [1, 2, 3, 0, 1, 2, 1, 0], [2, 1, 2, 3, 0, 1, 2, 1, 0]],
    [[1], [2, 1], [1, 2, 1], [3, 2, 1], [1, 2, 0, 1], [3, 1, 2, 1], [2, 1, 2, 0, 1]],
    [[1, 2], [2, 1, 2], [3, 1, 2], [2, 3, 1, 2], [3, 2, 1, 2], [1, 2, 3, 1, 2], [2, 3, 2, 1, 2]],
    [[1, 2, 3], [2, 1, 2, 3], [3, 2, 1, 2, 3], [1, 2, 3, 1, 2, 0, 1, 2, 3]]]

theorem tw2e6InnerPairs_length : ∀ (i : Fin 3) (b : Fin 4), (tw2e6InnerPairs i b).length = 4 := by
  decide

theorem tw2e6InnerPairs_nodup : ∀ (i : Fin 3) (b : Fin 4),
    ((tw2e6InnerPairs i b).map (fun w => w.foldr (reflect Tag.F4) (f4Weight b)) ++
      (tw2e6InnerPairs i b).map
        (fun w => (tw2e6InnerWord i ++ w).foldr (reflect Tag.F4) (f4Weight b))).Nodup := by
  decide +kernel

theorem tw2e6OuterPairs_length_of_ne : ∀ b : Fin 4, b ≠ 3 → (tw2e6OuterPairs b).length = 7 := by
  decide

theorem tw2e6OuterPairs_length_three : (tw2e6OuterPairs 3).length = 4 := by
  decide

theorem tw2e6OuterPairs_nodup : ∀ b : Fin 4,
    ((tw2e6OuterPairs b).map (fun w => w.foldr (reflect Tag.F4) (f4Weight b)) ++
      (tw2e6OuterPairs b).map
        (fun w => (([0] : List (Fin 4)) ++ w).foldr (reflect Tag.F4) (f4Weight b))).Nodup := by
  decide +kernel

end CFSG.LocalAnalysis.WeakClosure81
