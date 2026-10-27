
module

public import CFSG.Sporadic.Schreier.PairHeTriple1Base
import all CFSG.Sporadic.Schreier.PairHeTriple1Base

public import Certificates.Certificate2225

public section

namespace CFSG.Sporadic.Schreier.PairHe

open CFSG.Sporadic.Schreier.PairNative CFSG.Sporadic.HeldB

theorem partner_bound :
    countPair bs 7 wA conds heBlocks ≤ 322560 ∧
      (List.range 8330).countP (fun i => (heGen 0)[i]! == i) = 346 ∧
      (List.range 8330).countP (fun i => t1Arr[i]! == i) = 42 :=
  Certificates.certificate2225

end CFSG.Sporadic.Schreier.PairHe
