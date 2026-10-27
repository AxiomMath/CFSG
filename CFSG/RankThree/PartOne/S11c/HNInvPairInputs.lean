module

public import CFSG.Sporadic.HNOddCore.SixCheckInputs
public import CFSG.Sporadic.HNOddCore.ChainUtil
public import CFSG.RankThree.Native.HSMcLSmallData
public meta import CFSG.Sporadic.HNOddCore.SixCheckInputs
public meta import CFSG.Sporadic.HNOddCore.ChainUtil
public meta import CFSG.RankThree.Native.HSMcLSmallData

public section

namespace CFSG.RankThree.PartOne.HNRed.Native

open CFSG.Sporadic.HNOddCore CFSG.Sporadic.HNOddCore.Native CFSG.RankThree.Native

@[expose] def pairA : Array ℕ := dA om0Gens ++ (hs100Arr 0).map (· + 1100)

@[expose] def pairB : Array ℕ := dB om0Gens ++ (hs100Arr 1).map (· + 1100)

@[expose] def pairBase : List (Fin 1200) := [0, 2, 1, 6]

@[noinline, expose] def pairCheck : Bool :=
  chainCheck 1200 #[pairA, pairB] SixData.dWords pairBase SixData.dSizes

end CFSG.RankThree.PartOne.HNRed.Native
