
module

public import CFSG.Sporadic.HNSchreier.InvolCheckBase
public import CFSG.Sporadic.HNSchreier.RankData
public import CFSG.Sporadic.HNSchreier.FAData
public meta import CFSG.Sporadic.HNSchreier.InvolCheckBase
public meta import CFSG.Sporadic.HNSchreier.RankData
public meta import CFSG.Sporadic.HNSchreier.FAData

public section

namespace CFSG.Sporadic.HNSchreier.Native

open CFSG.Sporadic.He.Native CFSG.ONSchreier.Native

@[expose] def subId (M : Array (Array Nat)) : Array (Array Nat) :=
  Array.ofFn (n := 133) fun i => Array.ofFn (n := 133) fun j =>
    (M[i.val]![j.val]! + if i.val = j.val then 4 else 0) % 5

@[expose] def diagR (r : Nat) : Array (Array Nat) :=
  Array.ofFn (n := 133) fun i => Array.ofFn (n := 133) fun j =>
    if i.val = j.val ∧ i.val < r then 1 else 0

@[expose] def rankList : List Nat := [84, 84, 90, 84]

@[noinline, expose] def rankChecks (A B : Array (Array Nat))
    (C : Array (Array (Array (Array Nat)))) : Bool :=
  let regs := progRegsM (initRegsM A B) Data.subgroupProgram
  let hs := extendStrongM #[regs[1]!, regs[2]!] LocalData.strongWords
  C.size == 4 && FAData.sWords.size == 4 &&
    allBelowN 4 (fun k =>
      let M := subId (mword hs.1 hs.2 FAData.sWords[k]!)
      let c := C[k]!
      c.size == 4 && plettersOK 17 FAData.sWords[k]! &&
        mulM 5 133 c[0]! c[1]! == idM 133 && mulM 5 133 c[2]! c[3]! == idM 133 &&
        mulM 5 133 (mulM 5 133 c[0]! M) c[2]! == diagR rankList[k]!)

@[expose] def rankCertRows : Array (Array (Array (Array Nat))) :=
  #[#[rowsOf 5 133 RankData.rank1P, rowsOf 5 133 RankData.rank1Pi, rowsOf 5 133 RankData.rank1Q,
      rowsOf 5 133 RankData.rank1Qi],
    #[rowsOf 5 133 RankData.rank2P, rowsOf 5 133 RankData.rank2Pi, rowsOf 5 133 RankData.rank2Q,
      rowsOf 5 133 RankData.rank2Qi],
    #[rowsOf 5 133 RankData.rank3P, rowsOf 5 133 RankData.rank3Pi, rowsOf 5 133 RankData.rank3Q,
      rowsOf 5 133 RankData.rank3Qi],
    #[rowsOf 5 133 RankData.rank4P, rowsOf 5 133 RankData.rank4Pi, rowsOf 5 133 RankData.rank4Q,
      rowsOf 5 133 RankData.rank4Qi]]

end CFSG.Sporadic.HNSchreier.Native
