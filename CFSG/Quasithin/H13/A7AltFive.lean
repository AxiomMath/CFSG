module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.Quasithin.H13.A7

open Equiv Equiv.Perm Subgroup

theorem fix_four_of_normalizes_V0 : ∀ σ : Perm (Fin 5),
    σ * (swap 0 1 * swap 2 3) * σ⁻¹ ∈ ({1, swap 0 1 * swap 2 3, swap 0 2 * swap 1 3,
      swap 0 3 * swap 1 2} : Finset (Perm (Fin 5))) →
    σ * (swap 0 2 * swap 1 3) * σ⁻¹ ∈ ({1, swap 0 1 * swap 2 3, swap 0 2 * swap 1 3,
      swap 0 3 * swap 1 2} : Finset (Perm (Fin 5))) → σ 4 = 4 := by
  decide +kernel

theorem fixed_of_V0 : ∀ m : Fin 5 → ZMod 2, ∑ i, m i = 0 →
    (∀ i, m ((swap 0 1 * swap 2 3 : Perm (Fin 5)) i) = m i) →
    (∀ i, m ((swap 0 2 * swap 1 3 : Perm (Fin 5)) i) = m i) →
    ∀ σ : Perm (Fin 5), σ 4 = 4 → ∀ i, m (σ⁻¹ i) = m i := by
  decide +kernel

section Cube

variable {G : Type*} [Group G]

theorem conj_eq_of_cube {V : Subgroup G} (hV2 : ∀ a ∈ V, a * a = 1) {x z : G}
    (hx3 : x ^ 3 = 1) (hz : z ∈ V) (hxV : x ∈ normalizer (V : Set G))
    (hu : x * (x * z * x⁻¹ * z⁻¹) * x⁻¹ = x * z * x⁻¹ * z⁻¹) : x * z * x⁻¹ = z := by
  set u := x * z * x⁻¹ * z⁻¹ with hudef
  have hxz : x * z * x⁻¹ ∈ V := (mem_normalizer_iff.1 hxV z).1 hz
  have huV : u ∈ V := mul_mem hxz (inv_mem hz)
  have h1 : x * z * x⁻¹ = u * z := by rw [hudef]; group
  have h2 : x * (x * z * x⁻¹) * x⁻¹ = z := by
    calc x * (x * z * x⁻¹) * x⁻¹ = x * (u * z) * x⁻¹ := by rw [h1]
      _ = (x * u * x⁻¹) * (x * z * x⁻¹) := by group
      _ = u * (u * z) := by rw [hu, h1]
      _ = z := by rw [← mul_assoc, hV2 u huV, one_mul]
  have hx3' : x * x * x = 1 := by rw [← hx3, pow_succ, pow_two]
  calc x * z * x⁻¹ = x * (x * (x * z * x⁻¹) * x⁻¹) * x⁻¹ := by rw [h2]
    _ = (x * x * x) * z * (x * x * x)⁻¹ := by group
    _ = z := by rw [hx3']; group

end Cube

end CFSG.Quasithin.H13.A7
