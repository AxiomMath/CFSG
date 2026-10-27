module

public import Certificates.Certificate17282

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.ONPar

open CFSG.ONSchreier CFSG.ONSchreier.Native CFSG.PSL3Four.Native CFSG.Sporadic.ONOddCore
open CFSG.Sporadic.ON.Native (nPts)

theorem onp_v_cert :
    memIn TStrong Data.TChain.base onpVArr = true ∧
      restrictOK onpVArr Data.TPoints onpV32 = true ∧
      blockImgOK onpVArr Data.quotientBlocks onpVB = true :=
  ⟨Certificates.certificate17282.1, Certificates.certificate17282.2.1,
    Certificates.certificate17282.2.2.1⟩

theorem onp_x_cert :
    peq nPts (pcomp nPts onpXArr zArr) (pcomp nPts (pcomp nPts onpVArr zArr) onpXArr) = true ∧
      peq nPts (pcomp nPts onpXArr onpVArr) (pcomp nPts zArr onpXArr) = true ∧
      peq nPts (pcomp nPts onpXArr (pcomp nPts onpXArr onpXArr)) (pid nPts) = true :=
  ⟨Certificates.certificate17282.2.2.2.1, Certificates.certificate17282.2.2.2.2.1,
    Certificates.certificate17282.2.2.2.2.2.1⟩

theorem onp_mn_cert :
    memIn MStrong Data.MChain.base onpMArr = true ∧
      memIn MStrong Data.MChain.base onpNArr = true ∧
      peq nPts (pcomp nPts onpGArr zArr) (pcomp nPts tArr onpGArr) = true :=
  ⟨Certificates.certificate17282.2.2.2.2.2.2.1,
    Certificates.certificate17282.2.2.2.2.2.2.2.1,
    Certificates.certificate17282.2.2.2.2.2.2.2.2.1⟩

theorem onp_q_cert :
    peq nPts (pcomp nPts qArr qArr) zArr = true :=
  Certificates.certificate17282.2.2.2.2.2.2.2.2.2.1

theorem onp_comm_cert :
    invsOK 32 omegaEnum.tabs onpOmInv = true ∧ invsOK 32 t32Enum.tabs onpTInv = true ∧
      enumOK 32 onpCommGens onpCommEnum = true ∧
      onpCommEnum.tabs.all (fun t => t == idTab 32 || t == Data.T32z || t == onpV32 ||
        t == comp 32 Data.T32z onpV32) = true ∧
      onpCommEnum.tabs.any (fun t => t == Data.T32z) = true ∧
      onpCommEnum.tabs.any (fun t => t == onpV32) = true :=
  ⟨Certificates.certificate17282.2.2.2.2.2.2.2.2.2.2.1,
    Certificates.certificate17282.2.2.2.2.2.2.2.2.2.2.2.1,
    Certificates.certificate17282.2.2.2.2.2.2.2.2.2.2.2.2.1,
    Certificates.certificate17282.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    Certificates.certificate17282.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    Certificates.certificate17282.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1⟩

theorem onp_orbit_cert :
    orbitOK 120 onpRGens onpRGensInv onpVBar onpROrbit = true ∧ onpROrbit.tabs.size = 315 :=
  ⟨Certificates.certificate17282.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    Certificates.certificate17282.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.ONPar
