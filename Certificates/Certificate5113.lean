module

public import Mathlib
public import CFSG.GH74.KGroups.Generic3
public import CFSG.GH74.KGroups.Generic5
public import CFSG.GH74.KGroups.Generic7
public import CFSG.GH74.KGroups.M11Tables
public import CFSG.GH74.Generic.Shapes
public import CFSG.GH74.KGroups.CoverM11Inputs
import Certificates.Kernel.Misc.KGroups.C5113

public section

namespace Certificates

open CertificateChecks

open CertificateChecks.KernelMisc.C5113 in
open CFSG in
open CFSG.GH74 in
open CFSG.GH74.KGroups in
open CFSG.GH74.KGroups.M11 in
open CFSG.Certificates CFSG.Sporadic.Schreier CFSG.Blueprint CFSG.GH74 CFSG.GH74.Generic Subgroup in
theorem certificate5113 : (fw ^ 3 = 1 ∧ fw * sR ^ 4 * fw⁻¹ = sR ^ 4 ∧ fw * sR ^ 2 * fw⁻¹ = sT * sR)
    ∧ (fg1 * sT * fg1⁻¹ = sR ^ 4 ∧ fg2 * sT * fg2⁻¹ = sT * sR ^ 2)
    ∧ (Q.sift fw 0 = true)
    ∧ (Q.sift fg1 0 = true)
    ∧ (Q.sift fg2 0 = true) :=
  ⟨fw_rels, fg_rels, fw_sift, fg1_sift, fg2_sift⟩

end Certificates
