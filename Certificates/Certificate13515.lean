module

public import Certificates.Data.B3Spor3.He
public import CFSG.Sporadic.HeldB.CertPChain
public import CFSG.Open.GLADefs
import Certificates.Kernel.SporSch.HeThree.Facts

public section

namespace Certificates

open CertificateChecks

open CFSG.HardMathSupport.Solomon.Coordinator.B3S3 CFSG.Sporadic.HeldB in
theorem certificate13515 :
    (∀ x ∈ heP, orderOf x = 3 → ∃ c < 2, ∃ k ∈ heP, ∃ e : ℕ, (e = 1 ∨ e = 2) ∧
      x = k * CFSG.Monster.B.Co2.permOfArr 8330 heS3CaseX[c]! ^ e * k⁻¹) ∧
    (∀ c < 2, CFSG.Monster.B.Co2.permOfArr 8330 heS3CaseX[c]! ∈ heP ∧
      orderOf (CFSG.Monster.B.Co2.permOfArr 8330 heS3CaseX[c]!) = 3 ∧
      CFSG.Open.GLAPPrimeCoreOf 3
        (Subgroup.centralizer {CFSG.Monster.B.Co2.permOfArr 8330 heS3CaseX[c]!} ⊓ heP) = ⊥) ∧
    Nat.card ↥(Subgroup.centralizer {CFSG.Monster.B.Co2.permOfArr 8330 heS3CaseX[0]!} ⊓ heP) =
      7560 ∧
    Nat.card ↥(Subgroup.centralizer {CFSG.Monster.B.Co2.permOfArr 8330 heS3CaseX[1]!} ⊓ heP) =
      504 ∧
    Subgroup.closure (CFSG.RankThree.Native.permsA 8330 heS3C0Gens) =
      Subgroup.centralizer {CFSG.Monster.B.Co2.permOfArr 8330 heS3CaseX[0]!} ⊓ heP ∧
    Subgroup.closure (CFSG.RankThree.Native.permsA 8330 heS3QGens) ≤ heP ∧
    Nat.card ↥(Subgroup.closure (CFSG.RankThree.Native.permsA 8330 heS3QGens)) = 27 ∧
    ∀ i < 2, CFSG.Monster.B.Co2.Rep 8330 heS3QGens[i]!
      (CFSG.Monster.B.Co2.permOfArr 8330 heS3QGens[i]!) := KernelSporSch.HeThree.facts

end Certificates
