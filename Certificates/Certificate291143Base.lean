
module

public import CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.ComponentPrimary.Cover3
public import Certificates.Data.CFSGNative.ComponentPrimary.Cover3Th
import Certificates.Kernel.Th3.Lower
import Certificates.Kernel.Th3.Card
public import CFSG.Certificates.CosetTableShort
public import CFSG.Certificates.NativeSchreierCard
public import CFSG.GroupTheory.LocalCores.Fitting
public import CFSG.LocalAnalysis.SectionRank.Sporadic.OpsF2
public import CFSG.LocalAnalysis.SectionRank.Sporadic.OpsF3
public import CFSG.LocalAnalysis.SectionRank.Sporadic.OpsFp
public import CFSG.Sporadic.Recognition.CoverCubeTransfer

@[expose] public section

open CFSG.CosetTable CFSG.SectionRank.Native CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.ComponentPrimary

namespace Certificates

instance thMax6Cover3_neZero : NeZero thMax6Cover3.m := ⟨by decide⟩

end Certificates

