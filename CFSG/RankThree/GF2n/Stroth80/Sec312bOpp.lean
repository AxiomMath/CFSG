module

public import CFSG.RankThree.GF2n.Stroth80.Sec312bOppDich
public import CFSG.RankThree.GF2n.Stroth80.Sec312bOppEq

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG.RankThree.GF2n.Stroth80.Classify

theorem opp_glue (hX : TheoremXStatement)
    {G : Type} [Group G] (R N L₁ L₂ : Subgroup G) (hL₁ : L₁ ≤ R) (hL₂ : L₂ ≤ R)
    {K V : Type} [Field K] [Finite K] [CharP K 2] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V]
    (F : LinearMap.BilinForm K V) (hnd : F.Nondegenerate) (halt : F.IsAlt) (h4 : 4 ≤ Nat.card K)
    (hdim : 4 ≤ Module.finrank K V)
    (ρ : ↥R →* (V ≃ₗ[K] V)) (hker : ρ.ker = N.subgroupOf R)
    (hiso : ρ.range ≤ sympSubgroup F)
    (e₁ e₂ : V) (h12 : F e₁ e₂ ≠ 0)
    (hepr₁ : (L₁.subgroupOf R).map ρ ≤ pointRadSubgroup F e₁)
    (hepr₂ : (L₂.subgroupOf R).map ρ ≤ pointRadSubgroup F e₂)
    (heful₁ : ElationFull F (((L₁.subgroupOf R).map ρ : Subgroup (V ≃ₗ[K] V)) : Set _) e₁)
    (heful₂ : ElationFull F (((L₂.subgroupOf R).map ρ : Subgroup (V ≃ₗ[K] V)) : Set _) e₂)
    (hcases : ρ.range = sympSubgroup F ∨ ∃ Q₀ : QuadraticForm K V, Q₀.polarBilin = F ∧
      ρ.range = ⁅orthSubgroup Q₀, orthSubgroup Q₀⁆)
    (hSinv : ρ.range = sympSubgroup F → ∀ x : V, F x e₁ = 0 →
      ∀ g ∈ (L₁.subgroupOf R).map ρ, symTransvection halt x 1 * g * (symTransvection halt x 1)⁻¹ ∈
        (L₁.subgroupOf R).map ρ) :
    ∀ r ∈ R, ∃ x ∈ L₁ ⊔ L₂, x⁻¹ * r ∈ N := by
  have hA₁ : (L₁.subgroupOf R).map ρ ≤ ρ.range ⊓ pointRadSubgroup F e₁ :=
    le_inf (Subgroup.map_le_range _ _) hepr₁
  have hA₂ : (L₂.subgroupOf R).map ρ ≤ ρ.range ⊓ pointRadSubgroup F e₂ :=
    le_inf (Subgroup.map_le_range _ _) hepr₂
  have hdich := opp_dichotomy hX F hnd halt h4 hdim e₁ e₂ h12 _ _ hepr₁ hepr₂ heful₁ heful₂
  have hEq := opp_eq F hnd halt h4 hdim e₁ e₂ h12 _ _ ρ.range hiso hA₁ hA₂ heful₁ heful₂
    hcases hdich hSinv
  intro r hr
  have hmem : ρ ⟨r, hr⟩ ∈ ρ.range := ⟨⟨r, hr⟩, rfl⟩
  rw [← hEq, ← Subgroup.map_sup, ← Subgroup.subgroupOf_sup hL₁ hL₂] at hmem
  obtain ⟨y, hy, hyr⟩ := hmem
  refine ⟨(y : G), Subgroup.mem_subgroupOf.mp hy, ?_⟩
  have h1 : y⁻¹ * ⟨r, hr⟩ ∈ ρ.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hyr, inv_mul_cancel]
  rw [hker, Subgroup.mem_subgroupOf] at h1
  simpa using h1

end CFSG.RankThree.GF2n.Stroth80
