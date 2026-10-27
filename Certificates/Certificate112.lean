module

import Certificates.Certificate7
public import CFSG.Dihedral.BlueprintDefs
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.ASevenStructureFacts

namespace CertificateChecks.Batch112

open CFSG CFSG.GorensteinWalter

open DihedralBlueprint

local instance : DecidablePred (fun x : ASevenCertificateGroup => x ∈ a7V) :=
  fun x => by
    change Decidable (x = 1 ∨ x = a7t ∨ x = a7u ∨ x = a7t * a7u)
    infer_instance

local instance : Fintype a7V := Subtype.fintype _

local instance : Fintype (Equiv.Perm a7V) := inferInstance

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem a7V_permutation_normalizer_certificate :
    ∀ a : Equiv.Perm a7V, a 1 = 1 → ∃ x : ASevenCertificateGroup,
      (x * a7a * x⁻¹ = a7a ∨ x * a7a * x⁻¹ = a7a ^ 2) ∧
      ∀ v : a7V, (a v : ASevenCertificateGroup) = x * (v : ASevenCertificateGroup) * x⁻¹ := by
  decide +kernel

end CertificateChecks.Batch112

public section

namespace Certificates

open CertificateChecks

open CFSG CFSG.GorensteinWalter in
open DihedralBlueprint in
theorem certificate112 : (∀ a : Equiv.Perm a7V, a 1 = 1 → ∃ x : ASevenCertificateGroup,
      (x * a7a * x⁻¹ = a7a ∨ x * a7a * x⁻¹ = a7a ^ 2) ∧
      ∀ v : a7V, (a v : ASevenCertificateGroup) = x * (v : ASevenCertificateGroup) * x⁻¹) := by
  exact CertificateChecks.Batch112.a7V_permutation_normalizer_certificate

end Certificates
