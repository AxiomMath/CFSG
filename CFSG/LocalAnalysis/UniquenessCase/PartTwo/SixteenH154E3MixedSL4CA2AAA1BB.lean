module

public import Mathlib.Algebra.Group.End
public import Mathlib.Algebra.Group.Subgroup.Lattice

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

theorem s16h_sl4_fix_mul_le {V : Type*} [CommGroup V] {a b : MulAut V} {U₁ U₂ Z : Subgroup V}
    (hsup : U₁ ⊔ U₂ = ⊤) (hinf : U₁ ⊓ U₂ = Z)
    (ha₂ : ∀ u ∈ U₂, a u = u) (hb₁ : ∀ u ∈ U₁, b u = u)
    (haU₁ : ∀ u ∈ U₁, a u ∈ U₁) (hbU₂ : ∀ u ∈ U₂, b u ∈ U₂)
    (hfa : ∀ u ∈ U₁, a u * u⁻¹ ∈ Z → u ∈ Z) (hfb : ∀ u ∈ U₂, b u * u⁻¹ ∈ Z → u ∈ Z)
    {v : V} (hv : (a * b) v = v) : v ∈ Z := by
  have hvtop : v ∈ U₁ ⊔ U₂ := by rw [hsup]; exact Subgroup.mem_top v
  obtain ⟨u₁, hu₁, u₂, hu₂, rfl⟩ := Subgroup.mem_sup.1 hvtop
  have hmul : a u₁ * b u₂ = u₁ * u₂ := by
    have h1 : (a * b) (u₁ * u₂) = a u₁ * b u₂ := by
      rw [MulAut.mul_apply, map_mul, hb₁ u₁ hu₁, map_mul, ha₂ _ (hbU₂ u₂ hu₂)]
    rw [← h1]
    exact hv
  have hkey : a u₁ * u₁⁻¹ = u₂ * (b u₂)⁻¹ := by
    rw [eq_mul_inv_iff_mul_eq, mul_right_comm, hmul, mul_comm u₁ u₂, mul_inv_cancel_right]
  have hZ₁ : a u₁ * u₁⁻¹ ∈ Z := by
    rw [← hinf]
    refine ⟨Subgroup.mul_mem _ (haU₁ u₁ hu₁) (Subgroup.inv_mem _ hu₁), ?_⟩
    rw [hkey]
    exact Subgroup.mul_mem _ hu₂ (Subgroup.inv_mem _ (hbU₂ u₂ hu₂))
  have hu₁Z : u₁ ∈ Z := hfa u₁ hu₁ hZ₁
  have hZ₂ : b u₂ * u₂⁻¹ ∈ Z := by
    have : b u₂ * u₂⁻¹ = (a u₁ * u₁⁻¹)⁻¹ := by
      rw [hkey, mul_inv_rev, inv_inv]
    rw [this]
    exact Subgroup.inv_mem _ hZ₁
  have hu₂Z : u₂ ∈ Z := hfb u₂ hu₂ hZ₂
  exact Subgroup.mul_mem _ hu₁Z hu₂Z

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
