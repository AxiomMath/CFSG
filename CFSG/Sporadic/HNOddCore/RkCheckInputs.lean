module

public import CFSG.Sporadic.HNSchreier.RankCheck
public import CFSG.Sporadic.HNOddCore.RankData
public import CFSG.Sporadic.HNOddCore.InvData
public meta import CFSG.Sporadic.HNSchreier.RankCheck
public meta import CFSG.Sporadic.HNOddCore.RankData
public meta import CFSG.Sporadic.HNOddCore.InvData

public section

namespace CFSG.Sporadic.HNOddCore.Native

open CFSG.Sporadic.He.Native CFSG.ONSchreier.Native CFSG.Sporadic.HNSchreier
open CFSG.Sporadic.HNSchreier.Native

@[expose] def rankCertOK (M : Array (Array Nat)) (cs : Array (Array (Array Nat))) (r : Nat) : Bool :=
  cs.size == 4 && mulM 5 133 cs[0]! cs[1]! == idM 133 && mulM 5 133 cs[2]! cs[3]! == idM 133 &&
    mulM 5 133 (mulM 5 133 cs[0]! M) cs[2]! == diagR r

@[noinline, expose] def invRankChecksH (S Si : Array (Array (Array Nat))) (A : Array (Array Nat))
    (C : Array (Array (Array (Array Nat)))) : Bool :=
  C.size == 3 && plettersOK 17 InvData.t2Word && plettersOK 17 InvData.t4Word &&
    rankCertOK (subId (mword S Si InvData.t2Word)) C[0]! 56 &&
    rankCertOK (subId (mword S Si InvData.t4Word)) C[1]! 64 && rankCertOK (subId A) C[2]! 56

@[noinline, expose] def invRankChecks (A B : Array (Array Nat))
    (C : Array (Array (Array (Array Nat)))) : Bool :=
  invRankChecksH (extendStrongM #[(progRegsM (initRegsM A B) Data.subgroupProgram)[1]!,
      (progRegsM (initRegsM A B) Data.subgroupProgram)[2]!] LocalData.strongWords).1
    (extendStrongM #[(progRegsM (initRegsM A B) Data.subgroupProgram)[1]!,
      (progRegsM (initRegsM A B) Data.subgroupProgram)[2]!] LocalData.strongWords).2 A C

@[expose] def invRankRows : Array (Array (Array (Array Nat))) :=
  #[#[rowsOf 5 133 RankData.rankT2P, rowsOf 5 133 RankData.rankT2Pi, rowsOf 5 133 RankData.rankT2Q,
      rowsOf 5 133 RankData.rankT2Qi],
    #[rowsOf 5 133 RankData.rankT4P, rowsOf 5 133 RankData.rankT4Pi, rowsOf 5 133 RankData.rankT4Q,
      rowsOf 5 133 RankData.rankT4Qi],
    #[rowsOf 5 133 RankData.rankT6P, rowsOf 5 133 RankData.rankT6Pi, rowsOf 5 133 RankData.rankT6Q,
      rowsOf 5 133 RankData.rankT6Qi]]

end CFSG.Sporadic.HNOddCore.Native
