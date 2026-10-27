module

public import Certificates.Data.W4RowConjInv
public import CFSG.Monster.B.Fischer.PinnedChainData
public import CFSG.Sporadic.FischerOddCore.Fi22ExtCheckInputs
public import CFSG.Sporadic.Schreier.RuCore

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Row

open CFSG.QuasithinUnique.Setup.X1 CFSG.Sporadic.RuSchreier CFSG.Monster.B.Co2.Native
  CFSG.Monster.B.Fischer CFSG.Sporadic.FischerOddCore

@[expose] def fi22A0P : PArr := (fi22ChainGen 0, invCand 3510 (fi22ChainGen 0))

@[expose] def fi22A1P : PArr := (fi22ChainGen 1, invCand 3510 (fi22ChainGen 1))

@[expose] def fi22RepArr (k : ℕ) : Array ℕ := fi22ExtArr (21 + k)

@[expose] def fi22RepP (k : ℕ) : PArr := (fi22RepArr k, fi22RepArr k)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Row
