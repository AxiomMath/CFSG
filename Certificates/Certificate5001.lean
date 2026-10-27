module

public import CFSG.GH74.KGroups.L33TablesInputs
import Certificates.Kernel.PermCent.KL33OuterGlue

public section

namespace Certificates

open CFSG.Certificates.Kernel.PkCV.L33R.OuterGlue in
open CFSG.GH74.KGroups in
theorem certificate5001 :
    (∀ τ ∈ L33.QA.originalSubgroup, τ ^ 2 = 1 → τ ∉ L33.QP.originalSubgroup →
      ∀ ψ ∈ L33.QA.originalSubgroup, (∀ c ∈ L33.QP.originalSubgroup, c ^ 3 = 1 → c * τ = τ * c →
        ψ * c = c * ψ) → ψ = 1 ∨ ψ = τ) ∧
    (∀ τ ∈ L33.QA.originalSubgroup, τ ^ 2 = 1 → τ ∉ L33.QP.originalSubgroup →
      ∃ l ∈ L33.QP.originalSubgroup, ∃ c₁ ∈ L33.QP.originalSubgroup,
        ∃ c₂ ∈ L33.QP.originalSubgroup, c₁ ^ 3 = 1 ∧ c₂ ^ 3 = 1 ∧ c₁ ≠ 1 ∧ c₂ ≠ 1 ∧
        c₁ * τ = τ * c₁ ∧ c₂ * τ = τ * c₂ ∧ (c₁ * c₂) ^ 2 = 1 ∧ c₁ * c₂ ≠ 1 ∧
        τ * l * τ⁻¹ * l⁻¹ = c₁ * c₂) ∧
    (∀ v ∈ L33.QP.originalSubgroup, v ^ 2 = 1 → v ≠ 1 → ∀ ψ ∈ L33.QA.originalSubgroup,
      (∀ c ∈ L33.QP.originalSubgroup, c ^ 3 = 1 → c * v = v * c → ψ * c = c * ψ) →
      (ψ ^ 2 = 1 ∨ ψ ^ 2 = v) ∧ (ψ ∈ L33.QP.originalSubgroup → ψ ^ 2 = 1 → ψ = 1 ∨ ψ = v)) ∧
    (∀ v ∈ L33.QP.originalSubgroup, v ^ 2 = 1 → v ≠ 1 → ∃ φ ∈ L33.QA.originalSubgroup,
      ∀ ψ ∈ L33.QA.originalSubgroup, (∀ c ∈ L33.QP.originalSubgroup, c ^ 3 = 1 →
        c * v = v * c → ψ * c = c * ψ) → ∃ k : ℕ, ψ = φ ^ k) ∧
    (∀ ψ ∈ L33.QA.originalSubgroup, (∀ q ∈ L33.QS.originalSubgroup, q * ψ = ψ * q) →
      ψ ∈ L33.QS.originalSubgroup) ∧
    (∃ a ∈ L33.QP.originalSubgroup, ∃ b ∈ L33.QP.originalSubgroup, a ^ 3 = 1 ∧ b ^ 3 = 1 ∧
      a ≠ 1 ∧ b ≠ 1 ∧ a * L33.s0 = L33.s0 * a ∧ b * L33.s0 = L33.s0 * b ∧
      (a * b) ^ 3 = L33.s0) ∧
    (∀ ψ ∈ L33.QA.originalSubgroup, ψ ∉ L33.QP.originalSubgroup →
      (∀ q ∈ L33.QS.originalSubgroup, ψ * q * ψ⁻¹ ∈ L33.QS.originalSubgroup) →
      ∀ v ∈ L33.QS.originalSubgroup, v ^ 2 = 1 → v ≠ 1 →
      (∀ c ∈ L33.QP.originalSubgroup, c ^ 3 = 1 → c * v = v * c → ψ * c = c * ψ) → ψ ^ 2 = v →
      ∀ q ∈ L33.QS.originalSubgroup, q * v = v * q) ∧
    (∀ a ∈ L33.QS.originalSubgroup, a ^ 4 = 1 → a ^ 2 ≠ 1 →
      (∀ c ∈ L33.QP.originalSubgroup, c ^ 3 = 1 → c * a ^ 2 = a ^ 2 * c → c * a = a * c) →
      ∃ k ∈ L33.QP.originalSubgroup, k⁻¹ * a * k ∈ L33.QS.originalSubgroup ∧
        ∀ y ∈ L33.QS.originalSubgroup, y * (k⁻¹ * a * k) = (k⁻¹ * a * k) * y) :=
  ⟨l33_outCent3, l33_bang, l33_innerSq, l33_cyc, l33_sylCent, l33_word, l33_sylSq, l33_conj4⟩

end Certificates
