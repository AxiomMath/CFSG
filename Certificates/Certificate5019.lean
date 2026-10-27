module

public import CFSG.GH74.E2.SDExtGeneric
public import CFSG.GH74.E2.Ext2
public meta import Mathlib
public import CFSG.GH74.E2.SDExtCertInputs
import CFSG.GH74.E2.Alpha1Core
import CFSG.CharacterTheory.Semidihedral.Model
public import CFSG.GH74.E2.SD16Cert

public section

open CFSG
open CFSG.GH74
open CFSG.GH74.E2
open CFSG.GH74.E2.SDW
open CFSG.Semidihedral
attribute [local instance] CFSG.GH74.E2.SDW.instDecEqSD16MForCert

public section

open CFSG
open CFSG.GH74
open CFSG.GH74.E2
open CFSG.GH74.E2.SDW
open CFSG.Semidihedral
attribute [local instance] CFSG.GH74.E2.SDW.instDecEqSD16MForCert

namespace CertificateChecks.Batch5019

open CFSG
open CFSG.GH74
open CFSG.GH74.E2
open CFSG.GH74.E2.SDW
open CFSG.Semidihedral

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
private theorem sd16Nf_spec_0 : ∀ a : SD16M, sd16R ^ (sd16Nf a).1 * sd16S ^ (sd16Nf a).2 = a := by
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
private theorem sd16_relations_1 : sd16R ^ 8 = 1 ∧ sd16R ^ 4 ≠ 1 ∧ sd16S * sd16S = 1 ∧ sd16S ≠ 1 ∧
    sd16S * sd16R * sd16S⁻¹ = sd16R ^ 3 := by
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
private theorem sd16_central_inv_aux_2 : ∀ z : SD16M, (∀ w : SD16M, w * z = z * w) → z * z = 1 → z ≠ 1 →
    z = sd16R ^ 4 := by
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
private theorem mem_lstSD_3 : ∀ a : SD16M, a ∈ lstSD := by
  decide +kernel

end CertificateChecks.Batch5019

namespace Certificates

open CertificateChecks

open CFSG in
open CFSG.GH74 in
open CFSG.GH74.E2 in
open CFSG.GH74.E2.SDW in
open CFSG.Semidihedral in
theorem certificate5019 : (∀ a : SD16M, sd16R ^ (sd16Nf a).1 * sd16S ^ (sd16Nf a).2 = a)
    ∧ (sd16R ^ 8 = 1 ∧ sd16R ^ 4 ≠ 1 ∧ sd16S * sd16S = 1 ∧ sd16S ≠ 1 ∧
    sd16S * sd16R * sd16S⁻¹ = sd16R ^ 3)
    ∧ (∀ z : SD16M, (∀ w : SD16M, w * z = z * w) → z * z = 1 → z ≠ 1 →
    z = sd16R ^ 4)
    ∧ (∀ a : SD16M, a ∈ lstSD) := by
  exact ⟨CertificateChecks.Batch5019.sd16Nf_spec_0, CertificateChecks.Batch5019.sd16_relations_1, CertificateChecks.Batch5019.sd16_central_inv_aux_2, CertificateChecks.Batch5019.mem_lstSD_3⟩

end Certificates
