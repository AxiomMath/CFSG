module

public import CFSG.GH74.AS16.E2.Local3ChecksInputs
public import CFSG.GH74.KGroups.U33TablesInputs
import Certificates.Kernel.PermCent.KU33OuterGlue

public section

namespace Certificates

open CFSG.Certificates.Kernel.PkCV.U33R.OuterGlue

open CFSG in
open CFSG.GH74 in
open CFSG.GH74.AS16 in
open CFSG.GH74.AS16.E2 in
open CFSG.Certificates CFSG.Sporadic.Schreier CFSG.Blueprint CFSG.GH74.KGroups in
theorem certificate5002 : (∀ τ ∈ U33.QA.originalSubgroup, τ ^ 2 = 1 → τ ∉ U33.QP.originalSubgroup →
      ∀ ψ ∈ U33.QA.originalSubgroup, (∀ c ∈ U33.QP.originalSubgroup, c ^ 3 = 1 →
        c * τ = τ * c → ψ * c = c * ψ) → ψ = 1 ∨ ψ = τ)
    ∧ (∀ τ ∈ U33.QA.originalSubgroup, τ ^ 2 = 1 → τ ∉ U33.QP.originalSubgroup →
      ∃ l ∈ U33.QP.originalSubgroup, ∃ c₁ ∈ U33.QP.originalSubgroup,
        ∃ c₂ ∈ U33.QP.originalSubgroup, c₁ ^ 3 = 1 ∧ c₂ ^ 3 = 1 ∧ c₁ ≠ 1 ∧ c₂ ≠ 1 ∧
          c₁ * τ = τ * c₁ ∧ c₂ * τ = τ * c₂ ∧ (c₁ * c₂) ^ 2 = 1 ∧ c₁ * c₂ ≠ 1 ∧
          τ * l * τ⁻¹ * l⁻¹ = c₁ * c₂)
    ∧ (∀ v ∈ U33.QP.originalSubgroup, v ^ 2 = 1 → v ≠ 1 → ∀ ψ ∈ U33.QA.originalSubgroup,
      (∀ c ∈ U33.QP.originalSubgroup, c ^ 3 = 1 → c * v = v * c → ψ * c = c * ψ) →
      (ψ ^ 2 = 1 ∨ ψ ^ 2 = v) ∧
        (ψ ∈ U33.QP.originalSubgroup → ψ ^ 2 = 1 → ψ = 1 ∨ ψ = v))
    ∧ (∀ ψ ∈ U33.QA.originalSubgroup, (∀ q ∈ U33.QS.originalSubgroup, q * ψ = ψ * q) →
      ψ ∈ U33.QS.originalSubgroup)
    ∧ (∃ a ∈ U33.QP.originalSubgroup, ∃ b ∈ U33.QP.originalSubgroup, a ^ 3 = 1 ∧ b ^ 3 = 1 ∧
      a ≠ 1 ∧ b ≠ 1 ∧ a * U33.s0 = U33.s0 * a ∧ b * U33.s0 = U33.s0 * b ∧
      (a * b) ^ 3 = U33.s0)
    ∧ (∀ ψ ∈ U33.QA.originalSubgroup, ψ ∉ U33.QP.originalSubgroup →
      (∀ q ∈ U33.QS.originalSubgroup, ψ * q * ψ⁻¹ ∈ U33.QS.originalSubgroup) →
      ∀ v ∈ U33.QS.originalSubgroup, v ^ 2 = 1 → v ≠ 1 →
      (∀ c ∈ U33.QP.originalSubgroup, c ^ 3 = 1 → c * v = v * c → ψ * c = c * ψ) →
      ψ ^ 2 = v → ∀ q ∈ U33.QS.originalSubgroup, q * v = v * q)
    ∧ (∀ a ∈ U33.QS.originalSubgroup, a ^ 4 = 1 → a ^ 2 ≠ 1 →
      (∀ c ∈ U33.QP.originalSubgroup, c ^ 3 = 1 → c * a ^ 2 = a ^ 2 * c → c * a = a * c) →
      ∃ k ∈ U33.QP.originalSubgroup, k⁻¹ * a * k ∈ U33.QS.originalSubgroup ∧
        ∀ y ∈ U33.QS.originalSubgroup, y * (k⁻¹ * a * k) = (k⁻¹ * a * k) * y)
    ∧ (U33.t0 ∈ U33.QP.originalSubgroup ∧ U33.t0 ≠ 1 ∧ U33.t0 ^ 2 = 1 ∧
      ∃ c ∈ U33.QP.originalSubgroup, c ^ 3 = 1 ∧ c ≠ 1 ∧ c * U33.t0 = U33.t0 * c)
    ∧ (∀ x ∈ U33.QP.originalSubgroup, x ^ 27 = 1 → x ^ 3 = 1)
    ∧ (∀ g ∈ U33.QA.originalSubgroup, g ^ 3 = 1 → g ∈ U33.QP.originalSubgroup) :=
  ⟨u33_outCent3, u33_bang, u33_innerSq, u33_sylCent, u33_word, u33_sylSq, u33_conj4,
    u33_exists3, u33_exp, u33_inner3⟩

end Certificates
