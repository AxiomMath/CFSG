module

public import Certificates.Data.YamakiPres

public section

namespace CFSG.ClassicalInvolution.Sp62Rec.I1

open CFSG.ClassicalInvolution.Solomon73.Yamaki

@[expose] def relsW (_ : Unit := ()) : List (List (Fin 10 × Bool)) :=
  (List.finRange 10).map (fun i => posW [i, i]) ++
  ([0, 1, 2, 3, 4] : List (Fin 10)).flatMap (fun i =>
    (([0, 1, 2, 3, 4] : List (Fin 10)).filter fun j => i < j).map (fun j => posW [i, j, i, j])) ++
  ([0, 1, 2, 3] : List (Fin 10)).map (fun k => posW [5 + k, 6 + k, 5 + k, 6 + k, 5 + k, 6 + k]) ++
  ([0, 1, 2] : List (Fin 10)).flatMap (fun k =>
    (([2, 3, 4] : List (Fin 10)).filter fun l => k + 1 < l).map (fun l =>
      posW [5 + k, 5 + l, 5 + k, 5 + l])) ++
  ([0, 1, 2, 3] : List (Fin 10)).flatMap (fun k =>
    (([0, 1, 2, 3, 4] : List (Fin 10)).filter fun i => i ≠ k ∧ i ≠ k + 1).map (fun i =>
      posW [5 + k, i, 5 + k, i]) ++ [posW [5 + k, k, 5 + k, k + 1]]) ++
  [posW [9, 4, 9, 4]] ++
  ([0, 1, 2, 3] : List (Fin 10)).map (fun i => posW [9, i, 9, 4, i])

end CFSG.ClassicalInvolution.Sp62Rec.I1
