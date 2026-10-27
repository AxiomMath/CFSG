module

public import Certificates.Data.Kernel.AE6FN
public import Certificates.Data.A6h2Swap

public section

namespace CFSG.KC.A6h2Swap

open CFSG.KC.Enum CFSG.KC.YoshQ CFSG.KC.AE6F Certificates.AE6Model Certificates.A6h2Swap

@[expose] def pqW : List (List Nat × List Nat) :=
  [([], []), (kWords.getD 0 [], []), ([], kWords.getD 0 []), (kWords.getD 1 [], []),
    ([], kWords.getD 1 []), (kWords.getD 0 [] ++ kWords.getD 1 [], []),
    ([], kWords.getD 0 [] ++ kWords.getD 1 []), (kWords.getD 0 [] ++ kWords.getD 0 [], [])]

@[expose] def imW (k : Nat) (w : List Nat) : List Nat :=
  w.map fun i => (swapMap.getD k []).getD i 0

@[expose] noncomputable def swapKN (G : List Nat) : Bool :=
  (List.range 3).all fun k => kWords.all fun w => pqW.any fun pq =>
    eqN 360 9 (awN G (imW k w ++ swapConj.getD k [] ++ pq.2)) (awN G (swapConj.getD k [] ++ pq.1))

end CFSG.KC.A6h2Swap
