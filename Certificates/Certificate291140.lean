module

public import CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.ComponentPrimary.Cover3
public import Certificates.Data.CFSGNative.ComponentPrimary.Cover3Co3
import Certificates.Data.Kernel.Local3K
import Certificates.Data.Kernel.LaneChain
import Certificates.Kernel.TcGen.F2
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Common.JsonGz
import CFSG.Certificates.Kernel.Common.Repo
import Certificates.Kernel.Bounds.Family
import CFSG.Certificates.Kernel.LaneChainSound
import CFSG.Certificates.Kernel.Co1F2Sound
import CFSG.Sporadic.HS.SmallF2Spec
import CFSG.LocalAnalysis.SectionRank.Sporadic.LocalWitness
import CFSG.Certificates.Kernel.Local3KSound
import CFSG.Certificates.Kernel.F2WordSound
import CFSG.Certificates.Kernel.Misc.Coset.TableFact
import CFSG.Certificates.Kernel.Misc.Coset.PGFilter
import all CFSG.Blueprint.NativeSporadic
public import CFSG.Certificates.CosetTableShort
public import CFSG.Certificates.NativeSchreierCard
public import CFSG.GroupTheory.LocalCores.Fitting
public import CFSG.LocalAnalysis.SectionRank.Sporadic.OpsF2
public import CFSG.LocalAnalysis.SectionRank.Sporadic.OpsF3
public import CFSG.LocalAnalysis.SectionRank.Sporadic.OpsFp
public import CFSG.Sporadic.Recognition.CoverCubeTransfer

public section

open CFSG.CosetTable CFSG.SectionRank.Native CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.ComponentPrimary

namespace Certificates

open CertificateChecks

instance co3Max8Cover3_neZero : NeZero co3Max8Cover3.m := ⟨by decide⟩

end Certificates

