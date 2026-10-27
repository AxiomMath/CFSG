
module

public import Certificates.Certificate3009Base

public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.NativeSylowDefs
import Certificates.Kernel.OmegaEight.Bridge3009

public section

open CFSG.EvenSmallLie.OmegaEight

namespace Certificates

open CertificateChecks

open CFSG.EvenSmallLie.OmegaEight in
theorem certificate3009 : (CFSG.EvenSmallLie.OmegaEight.nsCheck = true)
    ∧ (CFSG.EvenSmallLie.OmegaEight.omegaChainCheck = true)
    ∧ (CFSG.EvenSmallLie.OmegaEight.autChainCheck = true)
    ∧ (omega1ChainCheck = true)
    ∧ (CFSG.EvenSmallLie.OmegaEight.sylowChainCheck = true)
    ∧ (CFSG.EvenSmallLie.OmegaEight.structureCheck = true)
    ∧ (stabCheck = true)
    ∧ (treeLitCheck = true)
    ∧ (sylowRepsLitCheck = true)
    ∧ (CFSG.EvenSmallLie.OmegaEight.cent0Check = true)
    ∧ SAFacts
    ∧ (CFSG.EvenSmallLie.OmegaEight.fgCheck = true)
    ∧ (CFSG.EvenSmallLie.OmegaEight.oddCheck = true)
    ∧ (CFSG.EvenSmallLie.OmegaEight.invsCheck = true) :=
  ⟨by decide +kernel, KernelO8.omegaChain_k, KernelO8.autChain_k, KernelO8.omega1Chain_k,
    KernelO8.sylowChain_k, KernelO8.structure_k, KernelO8.stab_k, KernelO8.tree_k,
    KernelO8.sylowReps_k, KernelO8.cent0_k, KernelO8.sa_facts_k, KernelO8.fg_k, KernelO8.odd_k,
    KernelO8.invs_k⟩

end Certificates
