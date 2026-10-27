module

public import CFSG.Certificates.InvariantMerge
import Certificates.Kernel.Sporadic.Fi22.C3155
public import CFSG.Monster.B.Fischer.Fi22CertBase

public section

namespace Certificates

open CertificateChecks

open CertificateChecks.KernelSpor.F3155 in
open CFSG.Monster.B.Fischer CFSG.Certificates in
theorem certificate3155 : fi22StabIdx = (List.range 19).filter (fun j => decide (fi22StrongPerm j 0 = 0)) ∧
      (∀ t < 3, {y : Fin 3510 | (y : ℕ) ∈ fi22StabOrbit t} =
        MulAction.orbit fi22H0 (fi22Pt ((fi22StabOrbit t).headD 0))) ∧
      (∀ y : Fin 3510, ∃ t < 3, (y : ℕ) ∈ fi22StabOrbit t) ∧
      ((List.range 3).map fun t => (fi22StabOrbit t).headD 0) = [0, 1, 11] ∧
      ValidInvariantMerge (fun k : Fin 2 => fi22GenPerm k) 0 (fi22Pt 1) (fi22MergeList 0) ∧
      ValidInvariantMerge (fun k : Fin 2 => fi22GenPerm k) 0 (fi22Pt 11) (fi22MergeList 1) :=
  ⟨idx_eq, fun _ ht => orbit_eq ht, cover, heads, merge_one, merge_eleven⟩

end Certificates
