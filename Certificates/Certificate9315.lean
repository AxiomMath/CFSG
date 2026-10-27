module

public import CFSG.ClassicalInvolution.SolvableCase.M12Inputs
public import CFSG.ClassicalInvolution.SmallCases.Sporadic.M12Inputs

public section

open CFSG CFSG.ClassicalInvolution
open CFSG CFSG.Open
open scoped MatrixGroups
open CFSG.Sporadic.Schreier (centralizerIn mem_centralizerIn)
open CFSG.Blueprint CFSG.Certificates CFSG.Sporadic.Mathieu CFSG.Sporadic.Schreier
  CFSG.Sporadic.Th CFSG.Sporadic.Schreier.Native

namespace CertificateChecks.Batch9315

open CFSG CFSG.ClassicalInvolution
open CFSG CFSG.Open
open scoped MatrixGroups
open CFSG.Sporadic.Schreier (centralizerIn mem_centralizerIn)
open CFSG.Blueprint CFSG.Certificates CFSG.Sporadic.Mathieu CFSG.Sporadic.Schreier
  CFSG.Sporadic.Th CFSG.Sporadic.Schreier.Native

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
private theorem m12_commutator_check :
    commutatorCheck (enumerationTab m12CentQ1) (permClosureList m12UGens1 20) 5 = true := by
  decide +kernel

end CertificateChecks.Batch9315

namespace Certificates

open CertificateChecks

open CFSG CFSG.ClassicalInvolution in
open CFSG CFSG.Open in
open scoped MatrixGroups in
open CFSG.Sporadic.Schreier (centralizerIn mem_centralizerIn) in
open CFSG.Blueprint CFSG.Certificates CFSG.Sporadic.Mathieu CFSG.Sporadic.Schreier
  CFSG.Sporadic.Th CFSG.Sporadic.Schreier.Native in
theorem certificate9315 : commutatorCheck (enumerationTab m12CentQ1) (permClosureList m12UGens1 20) 5 = true := by
  exact CertificateChecks.Batch9315.m12_commutator_check

end Certificates
