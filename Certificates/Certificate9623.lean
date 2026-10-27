module

public import Certificates.Data.ONanSmallM11
import CFSG.Certificates.Kernel.M11Local.Group
import Certificates.Kernel.M11Local.Codes

public section

namespace Certificates

open Certificates.ONanSmallM11 in
theorem certificate9623 :
    m11x ∈ CFSG.Blueprint.NativeSporadic.M11 ∧ m11y ∈ CFSG.Blueprint.NativeSporadic.M11 ∧
    m11s ∈ CFSG.Blueprint.NativeSporadic.M11 ∧ m11E.Nodup ∧
    (∀ a ∈ m11E, ∀ b ∈ m11E, a * b ∈ m11E) ∧ (∀ a ∈ m11E, a⁻¹ ∈ m11E) ∧
    m11x ^ 3 = 1 ∧ m11y ^ 3 = 1 ∧ m11x * m11y = m11y * m11x ∧ m11x ≠ 1 ∧
    m11y ∉ ([1, m11x, m11x ^ 2] : List (Equiv.Perm (Fin 11))) ∧
    (∀ g ∈ CFSG.Blueprint.NativeSporadic.M11, g 0 = 0 → g 1 = 1 → g 2 = 2 → g 3 = 3 → g = 1) ∧
    (∀ g ∈ CFSG.Blueprint.NativeSporadic.M11,
      (g * m11x * g⁻¹ ∈ m11E ∧ g * m11y * g⁻¹ ∈ m11E) ↔
        ((g 0 = 0 ∧ g 1 = 1) ∨ (g 0 = 1 ∧ g 1 = 0))) ∧
    (∀ g ∈ CFSG.Blueprint.NativeSporadic.M11, g * m11x = m11x * g → g * m11y = m11y * g →
      g ∈ m11E) ∧
    (∀ v ∈ m11E, v ≠ 1 → ∀ t ∈ m11E, t ≠ 1 → ∃ n ∈ CFSG.Blueprint.NativeSporadic.M11,
      ((n 0 = 0 ∧ n 1 = 1) ∨ (n 0 = 1 ∧ n 1 = 0)) ∧ n * v * n⁻¹ = t) ∧
    (((m11s 0 = 0 ∧ m11s 1 = 1) ∨ (m11s 0 = 1 ∧ m11s 1 = 0)) ∧ m11s ^ 8 = 1 ∧ m11s ^ 4 ≠ 1 ∧
      ∀ t ∈ m11E, t ≠ 1 → m11s * t * m11s⁻¹ ≠ t) :=
  CFSG.KC.M11L.m11_facts_of_check CertificateChecks.KernelM11Local.m11K_codes

end Certificates
