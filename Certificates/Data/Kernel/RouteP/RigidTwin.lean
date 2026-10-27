module

public import CFSG.Certificates.Kernel.Spor.PK.BFS

public section

namespace CFSG.KC.RouteP

open CFSG.KS.PK

@[expose] def orbitBS (F : Nat → Nat → Nat) (m n : Nat) : List BS :=
  ((List.range n).foldl (fun st r => if st.1.contains r then st else
      (st.1 ++ (BS.run F (List.range m) n r).pts, st.2 ++ [BS.run F (List.range m) n r]))
    (([] : List Nat), ([] : List BS))).2

@[expose] def propLF (F : Nat → Nat → Nat) (s : BS) (c : Nat) : Nat → Nat → Nat
  | 0, _ => c
  | f + 1, k => if 0 < k ∧ s.par.getD k 0 < k then F (s.lab.getD k 0) (propLF F s c f (s.par.getD k 0))
    else c

@[expose] def propL (F : Nat → Nat → Nat) (s : BS) (c k : Nat) : Nat := propLF F s c k k

@[expose] def candTw (F : Nat → Nat → Nat) (m : Nat) (s : BS) (c : Nat) : Bool :=
  (List.range s.pts.length).all fun k => (List.range m).all fun l =>
    propL F s c (s.pts.idxOf (F l (s.pts.getD k 0))) == F l (propL F s c k)

@[expose] def combinedTw (F : Nat → Nat → Nat) : List BS → List Nat → Nat → Nat
  | s :: ss, c :: cs, v => if s.pts.contains v then propL F s c (s.pts.idxOf v) else
    combinedTw F ss cs v
  | _, _, v => v

end CFSG.KC.RouteP
