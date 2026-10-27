module

public import Certificates.Data.Item434SporGenJ2HSMcL

public section

namespace CFSG.RankThree.PartTwo.Sec4.Item434SporGen

open CFSG.Monster.B.Co2.Native CFSG.Certificates.Native

@[expose] def mcl9Hex : String := include_str "Item434SporMcL9.txt"

@[expose, irreducible] def mcl9Arr (k : ℕ) : Array ℕ := hexTable 3 275 (275 * k) mcl9Hex

@[expose] def mcl9Code (a : ℕ) : ℕ := [34, 3, 38, 35].getD a 0

@[expose] def mcl9E (a : ℕ) : Array ℕ := mclDProd (mcl9Code a)

@[expose] def mcl9Prod (u : ℕ) : Array ℕ :=
  compA 275 (compA 275 (compA 275 (powN 275 (mcl9E 0) (u % 3))
    (powN 275 (mcl9E 1) (u / 3 % 3))) (powN 275 (mcl9E 2) (u / 9 % 3)))
    (powN 275 (mcl9E 3) (u / 27 % 3))

@[expose] def mcl9Check : Bool :=
  allLt 3 (fun k => mclSift (mcl9Arr k)) &&
    eqA 275 (conjN 275 (mcl9Arr 0) (mcl9E 0)) (mcl9E 0) &&
    eqA 275 (conjN 275 (mcl9Arr 0) (mcl9E 1)) (mcl9E 1) &&
    eqA 275 (conjN 275 (mcl9Arr 0) (mcl9E 2)) (powN 275 (mcl9E 2) 2) &&
    eqA 275 (conjN 275 (mcl9Arr 0) (mcl9E 3)) (powN 275 (mcl9E 3) 2) &&
    eqA 275 (conjN 275 (mcl9Arr 1) (mcl9E 0)) (mcl9E 0) &&
    eqA 275 (conjN 275 (mcl9Arr 1) (mcl9E 1)) (powN 275 (mcl9E 1) 2) &&
    eqA 275 (conjN 275 (mcl9Arr 1) (mcl9E 2)) (mcl9E 2) &&
    eqA 275 (conjN 275 (mcl9Arr 1) (mcl9E 3)) (powN 275 (mcl9E 3) 2) &&
    eqA 275 (conjN 275 (mcl9Arr 2) (mcl9E 1)) (mcl9Prod 73) &&
    allLt 81 (fun u => allLt 81 fun v => u == v || !eqA 275 (mcl9Prod u) (mcl9Prod v))

end CFSG.RankThree.PartTwo.Sec4.Item434SporGen
