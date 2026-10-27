module

public import CFSG.HardMathSupport.Foote.E27.LieTwo.OrthModel
import Certificates.Kernel.E27Orth.O10pGlue

public section

namespace Certificates

open Subgroup CFSG.HardMathSupport.Foote.E27 CFSG.Assembly.LowTwoRank in
theorem certificate131007 :
    ∃ S₀ B₀ : Subgroup ↥(OrthN (StatedQuadPlus 5 (ZMod 2))), Nat.card S₀ = 243 ∧
      Nat.card B₀ = 81 ∧
      S₀ ≤ (StatedOmega (StatedQuadPlus 5 (ZMod 2))).subgroupOf (OrthN (StatedQuadPlus 5 (ZMod 2))) ∧
      B₀ ≤ (StatedOmega (StatedQuadPlus 5 (ZMod 2))).subgroupOf (OrthN (StatedQuadPlus 5 (ZMod 2))) ∧
      (∀ x ∈ B₀, ∀ y ∈ B₀, x * y = y * x) ∧
      ∀ s ∈ S₀, s ^ 3 = 1 → s ≠ 1 → ∃ x : ↥(OrthN (StatedQuadPlus 5 (ZMod 2))), x * s * x⁻¹ ∈ B₀ :=
  CertificateChecks.KernelE27Orth.O10p.o10p131007_fact

end Certificates
