module

public import CFSG.Sporadic.SuzOddCore.InvPerms
import Certificates.Kernel.Sporadic.OddCore.S129061F
import CFSG.Sporadic.SuzOddCore.ArraysCheckInputs
import CFSG.Sporadic.SuzOddCore.SmallChainCheckInputs
meta import CFSG.Sporadic.SuzOddCore.ArraysCheck
meta import Certificates.Data.CFSGNative.Schreier.Check
import CFSG.GroupTheory.LocalCores.Fitting
import CFSG.GroupTheory.LocalCores.MinimalNormal
import CFSG.LocalAnalysis.ComponentClassification.AS76bHypII
import CFSG.Sporadic.SuzOddCore.GraphData
import CFSG.Sporadic.SuzOddCore.SmallActionData
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Borel
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Lemma83
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.GroupAction.Cardinalities
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PSL2Contragredient
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.ProjectiveSemilinear
import CFSG.Walter.Defs

public section

namespace Certificates

open CertificateChecks

open CFSG.Sporadic.SuzOddCore in
theorem certificate129061 : ∀ i < 4, ∃ g ∈ suzM, ∃ h ∈ suzM,
    suzM ≤ Subgroup.closure {suzInv i, g * suzInv i * g⁻¹, h * suzInv i * h⁻¹} := KernelSpor.S129061.gen_facts

end Certificates
