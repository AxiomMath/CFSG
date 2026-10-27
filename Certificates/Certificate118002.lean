module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Sp6CoverSpec
import Certificates.Kernel.Sp6Cover.Glue

public section

namespace Certificates

open CertificateChecks

open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Sp6CoverData
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Sp6Cover in
theorem certificate118002 :
    Nat.card ySub = 2903040 ∧
    (∀ k < 3, CFSG.Monster.B.Co2.Rep 240 yS[k]! (dP k)) ∧
    (∀ a ∈ [tA, iA, jA] ++ cA.toList,
      CFSG.Monster.B.Co2.Rep 240 a (CFSG.Monster.B.Co2.permOfArr 240 a)) ∧
    tP ∈ ySub ∧ iP ∈ ySub ∧ jP ∈ ySub ∧ (∀ k < 3, gP k ∈ ySub) ∧
    (∀ a ∈ cA.toList, CFSG.Monster.B.Co2.permOfArr 240 a ∈ CSub) ∧
    (∀ k < 3, (dP k)⁻¹ = tP * (gP k * tP * (gP k)⁻¹)) ∧
    tP * tP = 1 ∧ tP ≠ 1 ∧ iP * iP = tP ∧ jP * jP = tP ∧ jP * iP * jP⁻¹ = iP⁻¹ ∧
    Nat.card CSub = 4608 ∧
    (∀ c ∈ CSub, ∀ r ∈ RSub, c * r * c⁻¹ ∈ RSub) ∧
    (∀ M : Subgroup (Equiv.Perm (Fin 240)), M ≤ CSub →
      (∀ c ∈ CSub, ∀ m ∈ M, c * m * c⁻¹ ∈ M) → Odd (Nat.card M) → M = ⊥) ∧
    (∃ x ∈ CSub, x ^ 3 = 1 ∧ x * iP ≠ iP * x) ∧
    (∀ x ∈ CSub, x ^ 9 = 1 → (x * iP = iP * x ∧ x * jP = jP * x) ∨
      ∃ y ∈ CSub, y * iP = iP * y ∧ y * jP = jP * y ∧ x * y ≠ y * x) :=
  KernelSp6Cover.facts118002

end Certificates
