module

public import CFSG.RankThree.PartTwo.Sec21.FF81Defs

@[expose] public section

namespace CFSG.RankThree.PartTwo.Sec21.FF81

variable {G : Type} [Group G] [Finite G]

theorem FF81Hyp.cen_eq_bot_of_irreducible
    {B : Subgroup G} {X Y : Subgroup (MulAut ↥B)}
    (hYX : Y ≤ X)
    (hYnorm : ∀ σ : MulAut ↥B, σ ∈ X → ∀ y : MulAut ↥B, y ∈ Y → σ * y * σ⁻¹ ∈ Y)
    (hYne : Y ≠ ⊥)
    (hirr : ∀ U : Subgroup ↥B, (∀ σ : MulAut ↥B, σ ∈ X → Subgroup.map σ U = U) →
      U = ⊥ ∨ U = ⊤) :
    ∀ x : ↥B, (∀ y : MulAut ↥B, y ∈ Y → y x = x) → x = 1 := by
  let U : Subgroup ↥B :=
    { carrier := {x | ∀ y : MulAut ↥B, y ∈ Y → y x = x}
      one_mem' := by
        intro y _
        exact map_one y
      mul_mem' := by
        intro a b ha hb y hy
        rw [map_mul, ha y hy, hb y hy]
      inv_mem' := by
        intro a ha y hy
        rw [map_inv, ha y hy] }
  have hUmem : ∀ x : ↥B, x ∈ U ↔ ∀ y : MulAut ↥B, y ∈ Y → y x = x := fun _ => Iff.rfl
  have hU : ∀ σ : MulAut ↥B, σ ∈ X → Subgroup.map σ U = U := by
    intro σ hσ
    apply le_antisymm
    · intro x hx
      rw [Subgroup.mem_map] at hx
      obtain ⟨u, hu, rfl⟩ := hx
      rw [hUmem] at hu ⊢
      intro y hy
      have ht : σ⁻¹ * y * σ ∈ Y := by
        simpa using hYnorm σ⁻¹ (inv_mem hσ) y hy
      calc
        y (σ u) = σ ((σ⁻¹ * y * σ) u) := by
          rw [MulAut.mul_apply, MulAut.mul_apply, MulAut.apply_inv_self]
        _ = σ u := by rw [hu (σ⁻¹ * y * σ) ht]
    · intro x hx
      rw [hUmem] at hx
      have hx' : σ⁻¹ x ∈ U := by
        rw [hUmem]
        intro y hy
        have ht : σ * y * σ⁻¹ ∈ Y := hYnorm σ hσ y hy
        have htu : (σ * y * σ⁻¹) x = x := hx (σ * y * σ⁻¹) ht
        calc
          y (σ⁻¹ x) = σ⁻¹ (σ (y (σ⁻¹ x))) := by rw [MulAut.inv_apply_self]
          _ = σ⁻¹ ((σ * y * σ⁻¹) x) := by rw [MulAut.mul_apply, MulAut.mul_apply]
          _ = σ⁻¹ x := by rw [htu]
      have hmem : σ (σ⁻¹ x) ∈ Subgroup.map σ U :=
        Subgroup.mem_map_of_mem (σ : ↥B →* ↥B) hx'
      rw [MulAut.apply_inv_self] at hmem
      exact hmem
  rcases hirr U hU with hbot | htop
  · intro x hx
    have hxU : x ∈ U := by
      rw [hUmem]
      exact hx
    exact (Subgroup.eq_bot_iff_forall (H := U)).mp hbot x hxU
  · exfalso
    apply hYne
    rw [Subgroup.eq_bot_iff_forall]
    intro y hy
    apply MulEquiv.ext
    intro x
    have hxU : x ∈ U := by
      rw [htop]
      exact Subgroup.mem_top x
    rw [hUmem] at hxU
    simpa using hxU y hy

end CFSG.RankThree.PartTwo.Sec21.FF81
