module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.ONanParCheckInputs
public meta import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.ONanParCheckInputs
import Certificates.Kernel.Sporadic.ONPar.Final

public section

namespace Certificates

open CertificateChecks

open CFSG.ONSchreier CFSG.ONSchreier.Native CFSG.PSL3Four.Native CFSG.Sporadic.ONOddCore in
open CFSG.Sporadic.ON.Native (nPts) in
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.ONPar in
theorem certificate17282 : memIn TStrong Data.TChain.base onpVArr = true ∧
    restrictOK onpVArr Data.TPoints onpV32 = true ∧
    blockImgOK onpVArr Data.quotientBlocks onpVB = true ∧
    peq nPts (pcomp nPts onpXArr zArr) (pcomp nPts (pcomp nPts onpVArr zArr) onpXArr) = true ∧
    peq nPts (pcomp nPts onpXArr onpVArr) (pcomp nPts zArr onpXArr) = true ∧
    peq nPts (pcomp nPts onpXArr (pcomp nPts onpXArr onpXArr)) (pid nPts) = true ∧
    memIn MStrong Data.MChain.base onpMArr = true ∧
    memIn MStrong Data.MChain.base onpNArr = true ∧
    peq nPts (pcomp nPts onpGArr zArr) (pcomp nPts tArr onpGArr) = true ∧
    peq nPts (pcomp nPts qArr qArr) zArr = true ∧
    invsOK 32 omegaEnum.tabs onpOmInv = true ∧
    invsOK 32 t32Enum.tabs onpTInv = true ∧
    CFSG.PSL3Four.Native.enumOK 32 onpCommGens onpCommEnum = true ∧
    onpCommEnum.tabs.all (fun t => t == CFSG.PSL3Four.Native.idTab 32 || t == Data.T32z || t == onpV32 ||
      t == comp 32 Data.T32z onpV32) = true ∧
    onpCommEnum.tabs.any (fun t => t == Data.T32z) = true ∧
    onpCommEnum.tabs.any (fun t => t == onpV32) = true ∧
    orbitOK 120 onpRGens onpRGensInv onpVBar onpROrbit = true ∧
    onpROrbit.tabs.size = 315 := KernelSpor.ONPar.facts

end Certificates
