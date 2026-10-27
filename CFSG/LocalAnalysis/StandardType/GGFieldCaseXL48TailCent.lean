module

public import CFSG.LocalAnalysis.StandardType.GGFieldCaseXL48TailFrob

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly
open scoped commutatorElement

@[expose] def GGL48NbrFieldInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G)
    (L D J X B₂ : Subgroup G) (d y : G) (K U U₁ : Subgroup G),
    GGFieldCaseSetup p B Bs x L D J X B₂ d y K U U₁ →
      x ∉ ⁅Subgroup.normalizer (K : Set G), Subgroup.normalizer (K : Set G)⁆ ⊔ U₁

section Config

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem mem_of_maxPSubgroup_of_le_centralizer {p : ℕ} {H₀ P : Subgroup G} {x : G}
    (hxc : H₀ ≤ Subgroup.centralizer ({x} : Set G)) (hxH : x ∈ H₀) (hxp : x ^ p = 1)
    (hPp : IsPGroup p P) (hPH : P ≤ H₀)
    (hPmax : ∀ Q : Subgroup G, Q ≤ H₀ → IsPGroup p Q → P ≤ Q → Q = P) : x ∈ P := by
  have hPN : P ≤ Subgroup.normalizer (Subgroup.zpowers x : Set G) := by
    intro g hg
    apply Subgroup.centralizer_le_normalizer
    rw [Subgroup.mem_centralizer_iff]
    intro v hv
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hv
    have hgx : g * x = x * g := Subgroup.mem_centralizer_singleton_iff.mp (hxc (hPH hg))
    exact (Commute.zpow_left (show Commute x g from hgx.symm) k).eq
  have hQ := hPmax (P ⊔ Subgroup.zpowers x) (sup_le hPH (Subgroup.zpowers_le.mpr hxH))
    (IsPGroup.to_sup_of_normal_right' hPp (GGL48.isPGroup_zpowers_of_pow_eq_one hxp) hPN)
    le_sup_left
  rw [← hQ]
  exact Subgroup.mem_sup_right (Subgroup.mem_zpowers x)

end Config

end CFSG.StandardType

end
