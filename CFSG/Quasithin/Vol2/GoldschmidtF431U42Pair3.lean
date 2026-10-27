module

public import CFSG.Quasithin.Vol2.GoldschmidtF431U42Lat2
public import CFSG.Quasithin.Vol2.GoldschmidtF431U42Pair

public section

namespace CFSG.Quasithin.H13.F431.U42

open CFSG.Quasithin CFSG.Open U42F431
open scoped Pointwise

theorem conj_mem_closure {S : Set Y} {g : Y} (hS : ∀ s ∈ S, g * s * g⁻¹ ∈ Subgroup.closure S)
    {h : Y} (hh : h ∈ Subgroup.closure S) : g * h * g⁻¹ ∈ Subgroup.closure S := by
  refine Subgroup.closure_induction (p := fun x _ => g * x * g⁻¹ ∈ Subgroup.closure S)
    hS ?_ ?_ ?_ hh
  · simp only [mul_one, mul_inv_cancel]
    exact Subgroup.one_mem _
  · intro x y _ _ hx hy
    have : g * (x * y) * g⁻¹ = (g * x * g⁻¹) * (g * y * g⁻¹) := by
      simp only [mul_assoc, inv_mul_cancel_left]
    rw [this]
    exact Subgroup.mul_mem _ hx hy
  · intro x _ hx
    have : g * x⁻¹ * g⁻¹ = (g * x * g⁻¹)⁻¹ := by
      simp only [mul_inv_rev, inv_inv, mul_assoc]
    rw [this]
    exact Subgroup.inv_mem _ hx

@[expose] def sY (i : Fin 45) : Y := ⟨sT i, sT_mem i⟩

@[expose] def Vsub : Subgroup Y := Subgroup.closure {g | ∃ p : Fin 45, p ∈ L0S ∧ g = sY p}

theorem sY_mem_T {p : Fin 45} (hp : p ∈ L0S) : sY p ∈ T := by
  have hp' : p.val ∈ L0 := hp
  have h := misc_spec.2.2.2 p.val hp'
  obtain ⟨i, hi, hie⟩ := List.mem_iff_getElem.1 (List.contains_iff_mem.1 h)
  rw [mem_T_iff]
  refine ⟨i, by have := chkT_spec.1; omega, ?_⟩
  rw [List.getD_eq_getElem _ _ hi, hie, tpTab_getD _ p.2]
  exact repL_sT p

theorem Vsub_le_T : Vsub ≤ T := by
  rw [Vsub, Subgroup.closure_le]
  rintro _ ⟨p, hp, rfl⟩
  exact sY_mem_T hp

theorem sY_zero : sY 0 = xY := by
  apply Subtype.ext
  exact sT_zero

theorem Vsub_ne_bot : Vsub ≠ ⊥ := by
  intro h
  have hx : xY ∈ Vsub := by
    rw [← sY_zero]
    exact Subgroup.subset_closure ⟨0, zero_mem_L0S, rfl⟩
  rw [h, Subgroup.mem_bot] at hx
  have h1 : x45 = 1 := congrArg Subtype.val hx
  have : xL = idL := repL_unique repL_x (by rw [h1]; exact repL_one 45)
  revert this
  decide +kernel

theorem Vsub_isPGroup :
    IsPGroup 2 Vsub := isSylow_T.2.1.to_le Vsub_le_T

end CFSG.Quasithin.H13.F431.U42
