module

public import Certificates.Data.TriD4Phi
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434D42Perm
import Certificates.Kernel.D4.LiftFacts

public section

namespace Certificates

open CertificateChecks

open CFSG.RankThree.PartTwo.Sec4.Item434D42 CFSG.StandardType.TriD4TwoRow
  CFSG.RankThree.Native CFSG.Monster.B.Co2 in
theorem certificate707012 : (s0Cert ()).pts.size = 243 ∧
    (∀ i < 243, Rep 2457 (s0Cert ()).pts[i]! (permOfArr 2457 (s0Cert ()).pts[i]!) ∧
      permOfArr 2457 (s0Cert ()).pts[i]! ∈ Subgroup.closure (permsA 2457 (s0Gens ()))) ∧
    (∀ x ∈ Subgroup.closure (permsA 2457 (s0Gens ())), ∃ i < 243, Rep 2457 (s0Cert ()).pts[i]! x) ∧
    Nat.card (Subgroup.closure (permsA 2457 (s0Gens ()))) = 243 ∧
    (permOfArr 2457 (f0Arr ()) * d4Phi⁻¹ ∈ d4P) ∧
    
      ∀ y ∈ Subgroup.zpowers d4Phi ⊔ d4P, y ∉ d4P → y ^ 3 = 1 →
        ∃ t ∈ d4P, t ≠ 1 ∧ t ^ 2 = 1 ∧ y * t = t * y :=
  KernelD4.lift_facts

end Certificates
