module

public import CFSG.Monster.GMS.Leech.Main
public import CFSG.Monster.GMS.Griess13.ChecksUniqueness
public import CFSG.Sporadic.Co1.Module.Pairs
public import CFSG.Monster.GMS.Leech.OddPairs
public import CFSG.Sporadic.Co1.Module.OddCent

public section

namespace CFSG.Monster.GMS

theorem leechPairStatement :
    LeechPairStatement :=
  leechPairStatement_of co1ModuleUniqueness co1PairFacts

theorem leechStatement :
    LeechStatement :=
  leechStatement_of co1ModuleUniqueness co1PairFacts co1InvolutionFacts

theorem leechCosetStatement :
    LeechCosetStatement :=
  leechCosetStatement_of co1ModuleUniqueness co1InvolutionFacts

theorem leechInvolutionStatement :
    LeechInvolutionStatement :=
  leechInvolutionStatement_of co1ModuleUniqueness co1InvolutionFacts

theorem leechOddPairStatement :
    LeechOddPairStatement :=
  leechOddPairStatement_of co1ModuleUniqueness co1InvolutionFacts
    CFSG.Sporadic.Co1.Module.Odd.co1OddPairFacts

end CFSG.Monster.GMS
