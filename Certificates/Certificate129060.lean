module

public import CFSG.Sporadic.SuzOddCore.Perms
import Certificates.Kernel.Sporadic.OddCore.S129060F
import CFSG.Sporadic.SuzOddCore.ArraysCheckInputs
import CFSG.Sporadic.SuzOddCore.SmallChainCheckInputs
meta import CFSG.Sporadic.SuzOddCore.ArraysCheck
meta import Certificates.Data.CFSGNative.Schreier.Check
public import CFSG.Certificates.LiftedSchreierData
public import Mathlib
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
theorem certificate129060 : ∃ (A : Subgroup (Equiv.Perm (Fin 1782))) (g : Equiv.Perm (Fin 1782)), A ≤ suzM ∧
    g ∈ suzM ∧ Nat.card A = 243 ∧ (∀ a ∈ A, ∀ b ∈ A, a * b = b * a) ∧ (∀ a ∈ A, a ^ 3 = 1) ∧
    (∀ a ∈ A, g * a * g⁻¹ ∈ A) ∧ g ^ 11 = 1 ∧ ∃ a ∈ A, g * a * g⁻¹ ≠ a := KernelSpor.S129060.ag_facts

end Certificates
