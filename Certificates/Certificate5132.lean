module

public import CFSG.GH74.KGroups.TwoM12Syl3Inputs

public section

open CFSG
open CFSG.GH74
open CFSG.GH74.KGroups
open CFSG.GH74.KGroups.TwoM12
open CFSG.Certificates CFSG.Sporadic.Schreier CFSG.Sporadic.Mathieu CFSG.Blueprint Subgroup
open CFSG.ComponentClassification CFSG.ComponentClassification.M12Cover
open CFSG.GH74.E2 (Shape2M12)

namespace CertificateChecks.Batch5132

open CFSG
open CFSG.GH74
open CFSG.GH74.KGroups
open CFSG.GH74.KGroups.TwoM12
open CFSG.Certificates CFSG.Sporadic.Schreier CFSG.Sporadic.Mathieu CFSG.Blueprint Subgroup
open CFSG.ComponentClassification CFSG.ComponentClassification.M12Cover
open CFSG.GH74.E2 (Shape2M12)

private theorem Q27_valid_0 : Q27.check = true ∧ Q27.orderCertificate = 27 := by
  decide +kernel

end CertificateChecks.Batch5132

namespace Certificates

open CertificateChecks

set_option compiler.extract_closed false in
open CFSG in
open CFSG.GH74 in
open CFSG.GH74.KGroups in
open CFSG.GH74.KGroups.TwoM12 in
open CFSG.Certificates CFSG.Sporadic.Schreier CFSG.Sporadic.Mathieu CFSG.Blueprint Subgroup in
open CFSG.ComponentClassification CFSG.ComponentClassification.M12Cover in
open CFSG.GH74.E2 (Shape2M12) in
theorem certificate5132 : Q27.check = true ∧ Q27.orderCertificate = 27 := by
  exact CertificateChecks.Batch5132.Q27_valid_0

end Certificates
