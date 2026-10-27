
module

public import CFSG.Sporadic.HNSchreier.LocalCheckBase
public import CFSG.Sporadic.HNSchreier.FAData
public meta import CFSG.Sporadic.HNSchreier.LocalCheckBase
public meta import CFSG.Sporadic.HNSchreier.FAData

public section

namespace CFSG.Sporadic.HNSchreier.Native

open CFSG.ONSchreier.Native CFSG.Sporadic.Th.Native

@[expose] def tripleArr (m : Nat) : Array Nat :=
  Array.ofFn (n := 12) fun i => if i.val < 3 * m then
    (if i.val % 3 = 2 then i.val - 2 else i.val + 1) else i.val

@[expose] def fiveArr : Array Nat := #[1, 2, 3, 4, 0, 5, 6, 7, 8, 9, 10, 11]

@[noinline, expose] def faNatChecks : Bool :=
  let nS := extendStrong 12 #[natArr LocalData.natGen1, natArr LocalData.natGen2]
    LocalData.strongWords
  let nSi := pinvs 12 nS
  FAData.sWords.size == 4 &&
    allBelowN 4 (fun k => plettersOK 17 FAData.sWords[k]! &&
      peq 12 (pword 12 nS nSi FAData.sWords[k]!) (tripleArr (k + 1))) &&
    plettersOK 17 FAData.fWord && peq 12 (pword 12 nS nSi FAData.fWord) fiveArr &&
    FAData.aWords.size == 5 &&
    allBelowN 5 (fun j => plettersOK 17 FAData.aWords[j]! &&
      allBelowN 5 fun i => (pword 12 nS nSi FAData.aWords[j]!)[i]! == i)

end CFSG.Sporadic.HNSchreier.Native
