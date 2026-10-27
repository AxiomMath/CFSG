module

public import Mathlib.GroupTheory.Sylow

public section

namespace CFSG.Quasithin.H13.U43

theorem exists_normalizer_lift {𝒦 Q : Type*} [Group 𝒦] [Finite 𝒦] [Group Q] (φ : 𝒦 →* Q)
    {p : ℕ} [Fact p.Prime] (P : Sylow p 𝒦) {g : 𝒦}
    (hg : φ g ∈ Subgroup.normalizer (((P : Subgroup 𝒦).map φ : Subgroup Q) : Set Q)) :
    ∃ m : 𝒦, m ∈ Subgroup.normalizer ((P : Subgroup 𝒦) : Set 𝒦) ∧
      ∃ s ∈ (P : Subgroup 𝒦).map φ, φ m = φ g * s := by
  classical
  set S : Subgroup Q := (P : Subgroup 𝒦).map φ with hS
  set N' : Subgroup 𝒦 := (Subgroup.normalizer (S : Set Q)).comap φ with hN'
  set X : Subgroup 𝒦 := S.comap φ with hX
  have hXN : X ≤ N' := fun x hx => Subgroup.le_normalizer hx
  have hPX : (P : Subgroup 𝒦) ≤ X := fun x hx => Subgroup.mem_map_of_mem φ hx
  have hPN : (P : Subgroup 𝒦) ≤ N' := hPX.trans hXN
  let X' : Subgroup ↥N' := X.subgroupOf N'
  have hnorm : X'.Normal := ⟨fun y hy n => by
    have hy' : φ (y : 𝒦) ∈ S := hy
    have hn' := Subgroup.mem_normalizer_iff.mp n.2
    show φ ((n : 𝒦) * (y : 𝒦) * (n : 𝒦)⁻¹) ∈ S
    rw [map_mul, map_mul, map_inv]
    exact (hn' _).1 hy'⟩
  let P' : Sylow p ↥N' := P.subtype hPN
  have hP'X' : (P' : Subgroup ↥N') ≤ X' := by
    intro x hx
    exact hPX hx
  have hfr := Sylow.normalizer_sup_eq_top' (N := X') P' hP'X'
  have hgN : g ∈ N' := hg
  have hmem : (⟨g, hgN⟩ : ↥N') ∈ Subgroup.normalizer (P' : Set ↥N') ⊔ X' := by
    rw [hfr]
    exact Subgroup.mem_top _
  obtain ⟨a, ha, b, hb, hab⟩ := Subgroup.mem_sup_of_normal_right.mp hmem
  refine ⟨(a : 𝒦), ?_, (φ (b : 𝒦))⁻¹, ?_, ?_⟩
  · have hP'coe : (P' : Subgroup ↥N') = (P : Subgroup 𝒦).subgroupOf N' := rfl
    have h1 : a ∈ Subgroup.normalizer
        (((P : Subgroup 𝒦).subgroupOf N' : Subgroup ↥N') : Set ↥N') := by
      rw [← hP'coe]
      exact ha
    rw [← Subgroup.subgroupOf_normalizer_eq hPN] at h1
    exact h1
  · have hb' : φ (b : 𝒦) ∈ S := hb
    exact S.inv_mem hb'
  · have hg' : (g : 𝒦) = (a : 𝒦) * (b : 𝒦) := congrArg Subtype.val hab.symm
    have : (a : 𝒦) = g * (b : 𝒦)⁻¹ := by rw [hg']; group
    rw [this, map_mul, map_inv]

end CFSG.Quasithin.H13.U43
