module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.ThetaSpor.HeThreeInputs
public meta import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.ThetaSpor.HeThreeInputs
public meta import CFSG.Sporadic.HeldB.HeBlocks
public meta import Certificates.Data.CFSGNative.HeldB.Tests
public meta import Certificates.Data.CFSGNative.PairSchreier.Core
import Certificates.Kernel.SchreierFam.C12637K

public section

namespace Certificates

open CertificateChecks.KernelSchreierFam

open CFSG CFSG.Sporadic CFSG.Sporadic.HeldB CFSG.Certificates CFSG.Sporadic.Schreier in
open CFSG.Monster.B.Co2.Native CFSG.Certificates.Native CFSG.Sporadic.Schreier.Native in
open CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier.PairNative CFSG.Sporadic.HeldB.Native in
open CFSG.AGLEmbeddingD2.Wilson.ThetaSpor.He CFSG.AGLEmbeddingD2.Wilson.ThetaSpor.PrimCert in
theorem certificate12637 : (heThreeXA.check = true ∧ heThreeXA.orderCertificate = 2520 ∧
      primOK 35 heThreeLettersA heThreeTwA heThreeEwA = true)
    ∧ (heThreeXB.check = true ∧ heThreeXB.orderCertificate = 168 ∧
      primOK 8 heThreeLettersB heThreeTwB heThreeEwB = true ∧
      fourOK 8 heThreeLettersB heThreeFourB = true) :=
  ⟨⟨xa_check.1, xa_check.2, primA_12637K⟩,
    ⟨xb_check.1, xb_check.2, primB_12637K.1, primB_12637K.2⟩⟩

end Certificates
