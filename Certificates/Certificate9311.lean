module

public import CFSG.ClassicalInvolution.SmallCases.Sporadic.M12Inputs
import Certificates.Kernel.SmallSpor.M12Glue
public import CFSG.ClassicalInvolution.SmallCases.Sporadic.Basic
public import CFSG.Sporadic.Schreier.MathieuOddCoreM12

public section

namespace Certificates

open CertificateChecks

open CFSG CFSG.ClassicalInvolution in
open CFSG.Blueprint CFSG.Certificates CFSG.Sporadic.Mathieu CFSG.Sporadic.Schreier
  CFSG.Sporadic.Th CFSG.Sporadic.Schreier.Native in
theorem certificate9311 : (twoConstrainedCheck (enumerationTab m12CentQ1) (permClosureList m12UGens1 20) 5 = true)
    ∧ (indexTwoCheck m12Rep2 (enumerationTab m12CentQ2) (permClosureList m12NGens2 20) = true) :=
  ⟨KernelSmallSpor.M12.check9311a, KernelSmallSpor.M12.check9311b⟩

end Certificates
