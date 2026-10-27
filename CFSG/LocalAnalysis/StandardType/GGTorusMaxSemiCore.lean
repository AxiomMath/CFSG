module

public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import CFSG.LocalAnalysis.StandardType.GGTorusMaxSemiCoreAbel
import CFSG.LocalAnalysis.StandardType.GGTorusMaxSemiCoreCent

public section

namespace CFSG.StandardType.FrameRoute

theorem tmSemi_core {F : Type} [Field F] [Finite F] [CharP F 2] (d m : ℕ)
    (hdm : m % 2 = 1 ∨ d < 3 ^ (m / 2))
    {W : Type} [Group W] (hW1 : commutator W ≠ ⊥)
    (hW2 : ∀ n ≤ d, ∀ f : ↥(commutator W) →* Equiv.Perm (Fin n), f = 1)
    {M : Type} [Group M] [Finite M] (Z E M0 : Subgroup M) [E.Normal]
    (hZE : Z ≤ E) (hEM0 : E ≤ M0) (hM0 : M0.index ≤ 2)
    (hZ : Nat.card Z = 3) (hE : Nat.card E = 3 ^ (m + 1))
    (hZc : ∀ z ∈ Z, ∀ a ∈ E, z * a = a * z)
    (hcomm : ∀ a ∈ E, ∀ b ∈ E, a * b * a⁻¹ * b⁻¹ ∈ Z)
    (hexp : ∀ a ∈ E, a ^ 3 ∈ Z)
    (hirr : ∀ N : Subgroup M, Z ≤ N → N ≤ E → N.Normal → N = Z ∨ N = E)
    (hcent : ∀ x : M, (∀ e ∈ E, x * e * x⁻¹ * e⁻¹ ∈ Z) → x ∈ E)
    (π : M →* W) (hπs : Function.Surjective π) (hπk : π.ker = E)
    (ρ : ↥M0 →* GL (Fin d) F) (hρ : Function.Injective ρ)
    (hρZ : ∀ z : ↥M0, (z : M) ∈ Z → ∃ c : F,
      ((ρ z : GL (Fin d) F) : Matrix (Fin d) (Fin d) F) = Matrix.scalar (Fin d) c) :
    False := by
  let N : Subgroup M := E ⊓ Subgroup.centralizer (E : Set M)
  have hNiff : ∀ x : M, x ∈ N ↔ x ∈ E ∧ x ∈ Subgroup.centralizer (E : Set M) :=
    fun x => Subgroup.mem_inf
  have hZN : Z ≤ N := by
    intro z hz
    exact (hNiff z).mpr
      ⟨hZE hz, Subgroup.mem_centralizer_iff.mpr fun e he => (hZc z hz e he).symm⟩
  have hNE : N ≤ E := fun x hx => ((hNiff x).mp hx).1
  have hNnormal : N.Normal := inferInstance
  rcases hirr N hZN hNE hNnormal with hNZ | hNEq
  ·
    have hcenZ : ∀ a ∈ E, (∀ b ∈ E, a * b = b * a) → a ∈ Z := by
      intro a haE ha
      have haN : a ∈ N :=
        (hNiff a).mpr ⟨haE, Subgroup.mem_centralizer_iff.mpr fun b hb => (ha b hb).symm⟩
      rw [hNZ] at haN
      exact haN
    exact tmSemi_core_centerZ d m hdm Z E M0 hZE hEM0 hZ hE hZc hcomm hexp hcenZ ρ hρ hρZ
  ·
    have hEN : E ≤ N := hNEq.ge
    have hEodd : Odd (Nat.card E) := by
      rw [hE]
      exact Odd.pow (n := m + 1) (by decide : Odd (3 : ℕ))
    have hab : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a := by
      intro a ha b hb
      exact ((Subgroup.mem_centralizer_iff.mp ((hNiff a).mp (hEN ha)).2) b hb).symm
    have hcentA : ∀ x : M, (∀ e ∈ E, x * e = e * x) → x ∈ E := by
      intro x hx
      apply hcent x
      intro e he
      have hx1 : x * e * x⁻¹ * e⁻¹ = 1 := by
        rw [hx e he, mul_assoc e x x⁻¹, mul_inv_cancel, mul_one, mul_inv_cancel]
      rw [hx1]
      exact Z.one_mem
    exact tmSemi_core_abelian d hW1 hW2 E M0 hEM0 hM0 hEodd hab hcentA π hπs hπk ρ hρ

end CFSG.StandardType.FrameRoute

end
