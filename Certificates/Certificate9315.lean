module

public import CFSG.ClassicalInvolution.SolvableCase.M12Inputs
public import CFSG.ClassicalInvolution.SmallCases.Sporadic.M12Inputs
import Certificates.Kernel.SmallSpor.M12Glue

public section

namespace Certificates

open CertificateChecks

open CFSG CFSG.ClassicalInvolution in
open CFSG CFSG.Open in
open scoped MatrixGroups in
open CFSG.Sporadic.Schreier (centralizerIn mem_centralizerIn) in
open CFSG.Blueprint CFSG.Certificates CFSG.Sporadic.Mathieu CFSG.Sporadic.Schreier
  CFSG.Sporadic.Th CFSG.Sporadic.Schreier.Native in
theorem certificate9315 : commutatorCheck (enumerationTab m12CentQ1) (permClosureList m12UGens1 20) 5 = true := by
  exact KernelSmallSpor.M12.check9315

end Certificates
