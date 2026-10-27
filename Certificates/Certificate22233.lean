module

public import Certificates.Data.GrSLitL34FactsCF23ONOutK3Data
import Certificates.Kernel.ONOutK3.FOk
import Certificates.Kernel.ONOutK3.Strong
import Certificates.Kernel.ONOutK3.MatDefs
import Certificates.Kernel.ONOutK3.FChk
import CFSG.Certificates.Kernel.Common.Harness

public section

open CFSG.ComponentClassification.SolMax.ONOut CFSG.ONSchreier CFSG.ONSchreier.Native
  CFSG.Sporadic.ON.Native

namespace Certificates

open CertificateChecks

open CFSG.ComponentClassification.SolMax.ONOut CFSG.ONSchreier CFSG.ONSchreier.Native
  CFSG.Sporadic.ON.Native in
theorem certificate22233 :
    strongOK nPts (wordArr wA) (wordArr wB) sigStrong Data.strongWords = true ∧
    treeOK 161280 3 (arrStep hArrs) CFSG.ComponentClassification.SolMax.ONOut.base3 mPar mLab mIm = true ∧
    treeOK 161280 3 (arrStep vArrs) CFSG.ComponentClassification.SolMax.ONOut.base3 mPar mLab mSim = true ∧
    distinctOK 161280 mIm = true ∧
    tList.length ≤ 1344 ∧
    allBelowN 161280 cTest = true ∧
    (treeOK 60 2 fStep CFSG.ComponentClassification.SolMax.ONOut.base3 CFSG.ComponentClassification.SolMax.ONOut.fPar CFSG.ComponentClassification.SolMax.ONOut.fLab fIm && fIm.size == 60 && distinctOK 60 fIm &&
      fClosedOK && fNoZOK && fFixOK && fCommOK) = true :=
  ⟨KernelSpor.ONK3.sig_strong, KernelSpor.ONK3.m_tree, KernelSpor.ONK3.m_sim,
    KernelSpor.ONK3.m_distinct, KernelSpor.ONK3.tList_len, KernelSpor.ONK3.cover,
    KernelSpor.ONK3.f_ok⟩

end Certificates
