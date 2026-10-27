module

public import CFSG.Quasithin.Vol2.KGFactC31RuCoverNative
import Certificates.Kernel.Misc.RuCover.Final
import CFSG.Sporadic.Schreier.RuCheckBasicInputs
import CFSG.Sporadic.Schreier.RuCheckCentersInputs
meta import CFSG.Sporadic.Schreier.RuCheckSylow
import CFSG.Sporadic.Schreier.RuCheckChainsInputs
import CFSG.Sporadic.Schreier.RuCheckIsoInputs
import CFSG.Sporadic.Schreier.RuArrays
import CFSG.Certificates.NativeSetOrbit
import Certificates.Data.CFSGNative.Ru.Data
import CFSG.Sporadic.Presentation.RuExactInputs
import CFSG.Sporadic.Ru
import CFSG.Sporadic.Bridge.VecSurj
import CFSG.Sporadic.Presentation.RuExact
import Certificates.Data.CFSGNative.Bridge.SurjD
import TauCeti.GroupTheory.SpecificGroups.CFSG.Sporadic.Presentation
import CFSG.LieType.Multipliers.TitsCheckInputs
import CFSG.Sporadic.Recognition.RuMultiplierTables
import CFSG.Sporadic.Recognition.RuMultiplierInputs
import CFSG.Sporadic.Recognition.RuMultiplierData
import CFSG.Sporadic.Recognition.RuMultiplierIndex
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

theorem certificate7257 : CFSG.Quasithin.KGC31.RuCover.coverChk () = true := KernelMisc.RuCover.coverChk_true

end Certificates

end
