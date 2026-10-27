module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.GroupTheory.ThreeGroupActionFixedPoint
public import CFSG.RankThree.PartTwo.Sec21.FF79Vocab

@[expose] public section

namespace CFSG.RankThree.PartTwo.Sec21.FF81

open CFSG.RankThree.PartTwo.Sec21.FF79

variable {G : Type} [Group G] [Finite G]

def FF81ChainStabilizer (B B₁ : Subgroup G) (X : Subgroup (MulAut ↥B)) : Subgroup X where
  carrier := { σ | (∀ y : ↥B, y ∈ B₁.subgroupOf B → (σ : MulAut ↥B) y = y) ∧
    (∀ x : ↥B, ∃ y ∈ B₁.subgroupOf B, (σ : MulAut ↥B) x = x * y) }
  mul_mem' := by
    rintro σ τ hσ hτ
    constructor
    · intro y hy
      change ((σ : MulAut ↥B) * (τ : MulAut ↥B)) y = y
      rw [MulAut.mul_apply, hτ.1 y hy, hσ.1 y hy]
    · intro x
      obtain ⟨yτ, hyτ, hτx⟩ := hτ.2 x
      obtain ⟨yσ, hyσ, hσx⟩ := hσ.2 x
      refine ⟨yσ * yτ, Subgroup.mul_mem (B₁.subgroupOf B) hyσ hyτ, ?_⟩
      change ((σ : MulAut ↥B) * (τ : MulAut ↥B)) x = x * (yσ * yτ)
      rw [MulAut.mul_apply, hτx, map_mul, hσx, hσ.1 yτ hyτ, mul_assoc]
  one_mem' := by
    constructor
    · intro y _
      rfl
    · intro x
      exact ⟨1, (B₁.subgroupOf B).one_mem, by simp⟩
  inv_mem' := by
    rintro σ hσ
    constructor
    · intro y hy
      have h := hσ.1 y hy
      calc ((σ : MulAut ↥B)⁻¹) y = ((σ : MulAut ↥B)⁻¹) ((σ : MulAut ↥B) y) := by rw [h]
        _ = y := MulAut.inv_apply_self (M := ↥B) _ _
    · intro x
      obtain ⟨y, hy, hxy⟩ := hσ.2 x
      refine ⟨y⁻¹, Subgroup.inv_mem (B₁.subgroupOf B) hy, ?_⟩
      change ((σ : MulAut ↥B)⁻¹) x = x * y⁻¹
      have hyinv : ((σ : MulAut ↥B)⁻¹) y = y := by
        calc ((σ : MulAut ↥B)⁻¹) y
            = ((σ : MulAut ↥B)⁻¹) ((σ : MulAut ↥B) y) := by rw [hσ.1 y hy]
          _ = y := MulAut.inv_apply_self (M := ↥B) _ _
      have hx : ((σ : MulAut ↥B)⁻¹) x * y = x := by
        calc ((σ : MulAut ↥B)⁻¹) x * y
            = ((σ : MulAut ↥B)⁻¹) x * ((σ : MulAut ↥B)⁻¹) y := by rw [hyinv]
          _ = ((σ : MulAut ↥B)⁻¹) (x * y) := (map_mul _ _ _).symm
          _ = ((σ : MulAut ↥B)⁻¹) ((σ : MulAut ↥B) x) := by rw [hxy]
          _ = x := MulAut.inv_apply_self (M := ↥B) _ _
      calc ((σ : MulAut ↥B)⁻¹) x = (((σ : MulAut ↥B)⁻¹) x * y) * y⁻¹ := by
            rw [mul_assoc, mul_inv_cancel, mul_one]
        _ = x * y⁻¹ := by rw [hx]

theorem FF81ChainStabilizer.normal (B B₁ : Subgroup G) (X : Subgroup (MulAut ↥B))
    (hX : ∀ x ∈ X, Subgroup.map (x : MulAut ↥B) (B₁.subgroupOf B) = B₁.subgroupOf B) :
    (FF81ChainStabilizer B B₁ X).Normal := by
  have hX_mem : ∀ {x : MulAut ↥B} (_ : x ∈ X) {y : ↥B},
      y ∈ B₁.subgroupOf B → x y ∈ B₁.subgroupOf B := by
    intro x hx y hy
    have hmem : x y ∈ Subgroup.map (x : ↥B →* ↥B) (B₁.subgroupOf B) :=
      Subgroup.mem_map_of_mem (x : ↥B →* ↥B) hy
    rwa [hX x hx] at hmem
  refine ⟨fun n hn g => ?_⟩
  have hg : (g : MulAut ↥B) ∈ X := g.2
  have hg'inv : ((g : MulAut ↥B)⁻¹) ∈ X := by
    simpa using Subgroup.inv_mem X hg
  constructor
  · intro y hy
    have h1 : ((g : MulAut ↥B)⁻¹) y ∈ B₁.subgroupOf B := hX_mem hg'inv hy
    change ((g : MulAut ↥B) * (n : MulAut ↥B) * (g : MulAut ↥B)⁻¹) y = y
    rw [MulAut.mul_apply, MulAut.mul_apply, hn.1 _ h1, MulAut.apply_inv_self]
  · intro x
    obtain ⟨y, hy, hny⟩ := hn.2 (((g : MulAut ↥B)⁻¹) x)
    refine ⟨(g : MulAut ↥B) y, hX_mem hg hy, ?_⟩
    change ((g : MulAut ↥B) * (n : MulAut ↥B) * (g : MulAut ↥B)⁻¹) x =
      x * ((g : MulAut ↥B) y)
    rw [MulAut.mul_apply, MulAut.mul_apply, hny, map_mul, MulAut.apply_inv_self]

end CFSG.RankThree.PartTwo.Sec21.FF81
