module

public import CFSG.Sporadic.HNOddCore.XCheckInputs
public import CFSG.Sporadic.HNOddCore.NatCheckInputs
public meta import CFSG.Sporadic.HNOddCore.XCheckInputs
public meta import CFSG.Sporadic.HNOddCore.NatCheckInputs

public section

namespace CFSG.RankThree.PartOne.HNRed.Native

open CFSG.ONSchreier.Native CFSG.Sporadic.HNSchreier CFSG.Sporadic.HNSchreier.Native
open CFSG.Sporadic.F5.Native CFSG.Sporadic.He.Native CFSG.Sporadic.HNOddCore.Native

@[expose] def sevenWord : List Int := [3, 4, 5]

@[expose] def cyc7 : List Nat := [0, 4, 11, 7, 3, 5, 2, 6, 8, 9, 10, 1]

@[noinline, expose] def sevenChecksH (n : Nat) (hS : Array (Array Nat)) : Bool :=
  plettersOK 17 sevenWord && fixedSet n #[pword n hS (pinvs n hS) sevenWord] == [0]

@[noinline, expose] def sevenChecksR (n : Nat) (regs : Array (Array Nat)) : Bool :=
  sevenChecksH n (extendStrong n #[regs[1]!, regs[2]!] LocalData.strongWords)

@[noinline, expose] def sevenChecksO (O : VOrbit) : Bool :=
  sevenChecksR hnsData.n
    (progRegs hnsData.n (initRegs hnsData.n (natTab O.alpha) (natTab O.beta)) Data.subgroupProgram)

@[noinline, expose] def sevenNatCheck : Bool :=
  natOK (extendStrong 12 #[natArr LocalData.natGen1, natArr LocalData.natGen2]
    LocalData.strongWords) (pinvs 12 (extendStrong 12 #[natArr LocalData.natGen1,
    natArr LocalData.natGen2] LocalData.strongWords)) sevenWord (natArr cyc7)

end CFSG.RankThree.PartOne.HNRed.Native
