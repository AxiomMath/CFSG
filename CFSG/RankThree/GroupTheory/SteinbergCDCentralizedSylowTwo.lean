module

public import CFSG.GroupTheory.SolvableHallNodes
public import CFSG.LocalAnalysis.SignalizerFunctor.InvariantSylowContainment

public section

namespace CFSG.RankThree.GroupTheory

open scoped Pointwise

theorem centralized_sylow_two_controls_invariant_two_subgroups {p : ℕ} [Fact p.Prime]
    {B N : Type*} [Group B] [Group N] [Finite B] [Finite N] [MulDistribMulAction B N]
    (hB : IsPGroup p B) (hp : ¬ p ∣ Nat.card N) (T : Sylow 2 N)
    (hT : ∀ b : B, ∀ x ∈ (T : Subgroup N), b • x = x) (U : Subgroup N) (hU2 : IsPGroup 2 U)
    (hU : ∀ b : B, ∀ x ∈ U, b • x ∈ U) :
    ∀ b : B, ∀ x ∈ U, b • x = x := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcop : Nat.Coprime p (Nat.card N) := (Nat.Prime.coprime_iff_not_dvd Fact.out).mpr hp
  obtain ⟨P, hUP, hPinv⟩ := CFSG.SignalizerFunctor.Helpers.invariant_sylow_containing p 2
    Fact.out Nat.prime_two hB hcop U hU2 hU
  have hP : ∀ b : B, ∀ x ∈ (P : Subgroup N), b • x ∈ (P : Subgroup N) := by
    intro b x hx
    have heq : b • (P : Subgroup N) = (P : Subgroup N) := by
      rw [← Sylow.pointwise_smul_def, hPinv b]
    rw [← heq]
    exact Subgroup.smul_mem_pointwise_smul x b _ hx
  have hTinv : ∀ b : B, ∀ x ∈ (T : Subgroup N), b • x ∈ (T : Subgroup N) := fun b x hx => by
    rw [hT b x hx]
    exact hx
  obtain ⟨c, hc, hPT⟩ := CFSG.SolvableHall.coprime_invariant_sylow_conjugacy hB hp P T hP hTinv
  intro b x hx
  have hxc : c⁻¹ * x * c ∈ (T : Subgroup N) := by
    rw [← hPT]
    refine ⟨x, hUP hx, ?_⟩
    simp
  have hbc : b • c = c := hc b
  have h := hT b _ hxc
  rw [smul_mul', smul_mul', smul_inv', hbc] at h
  simpa using h

end CFSG.RankThree.GroupTheory
