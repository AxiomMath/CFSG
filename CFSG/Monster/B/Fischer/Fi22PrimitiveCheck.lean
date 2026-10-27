module

public import Certificates.Certificate3155

public section

namespace CFSG.Monster.B.Fischer

open CFSG.Certificates

theorem fi22Primitive_check :
    fi22StabIdx = (List.range 19).filter (fun j => decide (fi22StrongPerm j 0 = 0)) ∧
    (∀ t < 3, {y : Fin 3510 | (y : ℕ) ∈ fi22StabOrbit t} =
      MulAction.orbit fi22H0 (fi22Pt ((fi22StabOrbit t).headD 0))) ∧
    (∀ y : Fin 3510, ∃ t < 3, (y : ℕ) ∈ fi22StabOrbit t) ∧
    ((List.range 3).map fun t => (fi22StabOrbit t).headD 0) = [0, 1, 11] ∧
    ValidInvariantMerge (fun k : Fin 2 => fi22GenPerm k) 0 (fi22Pt 1) (fi22MergeList 0) ∧
    ValidInvariantMerge (fun k : Fin 2 => fi22GenPerm k) 0 (fi22Pt 11) (fi22MergeList 1) :=
  Certificates.certificate3155

end CFSG.Monster.B.Fischer
