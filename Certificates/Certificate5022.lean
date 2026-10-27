module

public import CFSG.GH74.Filter.Statements
public import Certificates.Data.CFSGNative.Filter.TitsElem
import Certificates.Kernel.LocalComp.Tits.Elem
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.SectionRank.Sporadic.TitsLocal

public section

open CFSG
open CFSG.GH74
open CFSG.GH74.Filter
open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree CFSG.LieType.Simplicity CFSG.SectionRank CFSG.SectionRank.TitsGen CFSG.SectionRank.TitsOrder CFSG.SectionRank.Native.Tits CFSG.SectionRank.TitsLocal CFSG.Sporadic.Th CFSG.Perm CFSG.Perm.Native
open CFSG.Sporadic.Th.Native (ap invT invOK idT compT powT Table allIn wordT)
attribute [local instance] idxAction

public section

namespace Certificates

open CertificateChecks

open CFSG in
open CFSG.GH74 in
open CFSG.GH74.Filter in
open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree CFSG.LieType.Simplicity CFSG.SectionRank CFSG.SectionRank.TitsGen CFSG.SectionRank.TitsOrder CFSG.SectionRank.Native.Tits CFSG.SectionRank.TitsLocal CFSG.Sporadic.Th CFSG.Perm CFSG.Perm.Native in
open CFSG.Sporadic.Th.Native (ap invT invOK idT compT powT Table allIn wordT) in
theorem certificate5022 : elemOK [0] [2, 26] [5, 6, 5] [16, 2, 5] [24, 2, 18] = true := KernelLC.Tits.elem

end Certificates
