
module

public import CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.ComponentPrimary.Cover3
public import Certificates.Data.CFSGNative.ComponentPrimary.Cover3Ly
import Certificates.Kernel.Ly3.Lower
import Certificates.Kernel.Ly3.Card
public import CFSG.Certificates.CosetTableShort
public import CFSG.Certificates.NativeSchreierCard
public import CFSG.GroupTheory.LocalCores.Fitting
public import CFSG.LocalAnalysis.SectionRank.Sporadic.OpsF2
public import CFSG.LocalAnalysis.SectionRank.Sporadic.OpsF3
public import CFSG.LocalAnalysis.SectionRank.Sporadic.OpsFp
public import CFSG.Sporadic.Recognition.CoverCubeTransfer
import Certificates.Kernel.Ly3.QAct
import Certificates.Kernel.Ly3.ZOne

@[expose] public section

open CFSG.CosetTable CFSG.SectionRank.Native CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.ComponentPrimary

namespace Certificates

instance lyMax7Cover3_neZero : NeZero lyMax7Cover3.m := ⟨by decide⟩

end Certificates

