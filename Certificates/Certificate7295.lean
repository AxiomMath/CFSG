module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoRu.SzCoverNative
import Certificates.Kernel.Misc.RuCoverNet.Final7295
import Certificates.Certificate15025
public import CFSG.Certificates.CosetTableCompactColumns
public import CFSG.Certificates.CosetTableShort
public import CFSG.Certificates.SeededRelations
public import CFSG.Certificates.WordSubgroupRel
public import CFSG.GroupTheory.LocalCores.Fitting
public import CFSG.Open.Defs
public import CFSG.Sporadic.Presentation.Common

public section

namespace Certificates

open CertificateChecks

theorem certificate7295 : CFSG.EvenSporadicStandard.TwoRu.SzCover.szCoverChk () = true := KernelMisc.RuCoverNet.szCoverChk_true

end Certificates

end
