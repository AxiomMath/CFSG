module

public import CFSG.Sporadic.Schreier.MathieuOddCoreModel
public import CFSG.Quasithin.Background.F7TwoInvSeed

public section

namespace CFSG.Quasithin.F7Two

open CFSG.Sporadic.Schreier CFSG.ComponentClassification.OuterAutomorphisms

variable {M : Type*} [Group M]

theorem invAutGen_of_inner_involutory (N : Subgroup M) (reps : Set M)
    (hZ : Subgroup.center N = ⊥)
    (hcov : ∀ u ∈ N, orderOf u = 2 → ∃ r ∈ reps, ∃ c ∈ N, u = c * r * c⁻¹)
    (hcls : ∀ r ∈ reps, ∀ x c : N, (x : M) = c * r * (c : M)⁻¹ →
      InvAutGen N (MulAut.conj x)) :
    ∀ φ : MulAut N, φ ∈ inner N → φ * φ = 1 → φ ≠ 1 → InvAutGen N φ := by
  rintro φ ⟨x, rfl⟩ hφ2 hφ1
  have hxx := mul_self_eq_one_of_conj_mul_self hZ hφ2
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hord : orderOf (x : M) = 2 := by
    refine orderOf_eq_prime ?_ ?_
    · rw [pow_two, ← Subgroup.coe_mul, hxx, Subgroup.coe_one]
    · intro h
      exact hφ1 (by rw [show x = 1 from Subtype.ext h, map_one])
  obtain ⟨r, hr, c, hc, hxc⟩ := hcov x x.2 hord
  exact hcls r hr x ⟨c, hc⟩ hxc

theorem invAutGen_of_outer_involutory (N : Subgroup M) [Finite N] (δ : M)
    (hδ : ∀ h ∈ N, δ * h * δ⁻¹ ∈ N) (hδ2 : δ * δ ∈ N) (hcenter : Subgroup.center N = ⊥)
    (houter : ∀ g ∈ N, ¬∀ h ∈ N, δ * g * h = h * (δ * g))
    (hcard : Nat.card (MulAut N) ≤ 2 * Nat.card N) (reps : Set M)
    (hcov : ∀ u, δ⁻¹ * u ∈ N → orderOf u = 2 → ∃ r ∈ reps, ∃ c ∈ N, u = c * r * c⁻¹)
    (hcls : ∀ r ∈ reps, ∀ (α : MulAut N) (u : M) (c : N), (∀ h : N, (α h : M) = u * h * u⁻¹) →
      u = c * r * (c : M)⁻¹ → InvAutGen N α) :
    ∀ α : MulAut N, α * α = 1 → α ∉ inner N → InvAutGen N α := by
  intro α hα2 hα
  have hδ' := inv_conj_mem N hδ hδ2
  obtain ⟨g, hg, hαg⟩ := exists_eq_conj_of_outer N δ hδ hδ2 hcenter houter hcard α hα
  set u := g * δ with hu_def
  have hu : δ⁻¹ * u ∈ N := by
    simpa [u, mul_assoc] using hδ' g hg
  have hu2N : u * u ∈ N := by
    have : u * u = g * (δ * g * δ⁻¹) * (δ * δ) := by simp only [u]; group
    rw [this]
    exact N.mul_mem (N.mul_mem hg (hδ g hg)) hδ2
  have hu2 : u * u = 1 := by
    have hc : (⟨u * u, hu2N⟩ : N) ∈ Subgroup.center N := by
      rw [Subgroup.mem_center_iff]
      intro z
      have hz := congrArg (fun φ : MulAut N => (φ z : M)) hα2
      simp only [MulAut.mul_apply, MulAut.one_apply] at hz
      rw [hαg, hαg] at hz
      apply Subtype.ext
      simp only [Subgroup.coe_mul]
      calc (z : M) * (u * u) = u * (u * z * u⁻¹) * u⁻¹ * (u * u) := by rw [hz]
        _ = u * u * z := by group
    rw [hcenter, Subgroup.mem_bot] at hc
    exact congrArg Subtype.val hc
  have hu1 : u ≠ 1 := by
    intro h1
    apply hα
    refine ⟨1, MulEquiv.ext fun z => Subtype.ext ?_⟩
    rw [hαg, h1]
    simp
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have ho : orderOf u = 2 := orderOf_eq_prime (by rw [sq]; exact hu2) hu1
  obtain ⟨r, hr, c, hc, huc⟩ := hcov u hu ho
  exact hcls r hr α u ⟨c, hc⟩ hαg huc

end CFSG.Quasithin.F7Two
