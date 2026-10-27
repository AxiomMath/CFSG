module

public import CFSG.Quasithin.Background.P3OrthoA8Data

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

open Matrix

namespace CFSG.Quasithin

namespace G11

namespace P3Ortho

@[expose] def wt (x : Fin 8 → ZMod 2) : ℕ := ∑ i, (x i).val

@[expose] def qP (x : Fin 8 → ZMod 2) : ZMod 2 := ((wt x / 2 : ℕ) : ZMod 2)

@[expose] def ones8 : Fin 8 → ZMod 2 := fun _ => 1

theorem wt_permAct (σ : Equiv.Perm (Fin 8)) (x : Fin 8 → ZMod 2) : wt (permAct σ x) = wt x := by
  unfold wt permAct
  exact Equiv.sum_comp σ⁻¹ (fun i => (x i).val)

theorem wt_cast (x : Fin 8 → ZMod 2) : ((wt x : ℕ) : ZMod 2) = ∑ i, x i := by
  simp [wt]

theorem two_dvd_wt {x : Fin 8 → ZMod 2} (hx : x ∈ permCore 8) : 2 ∣ wt x := by
  have h : ∑ i, x i = 0 := hx
  rw [← wt_cast] at h
  exact (ZMod.natCast_eq_zero_iff _ _).1 h

theorem wt_add_inter (x y : Fin 8 → ZMod 2) :
    wt (x + y) + 2 * ∑ i, (x i * y i).val = wt x + wt y := by
  unfold wt
  have h : ∀ a b : ZMod 2, (a + b).val + 2 * (a * b).val = a.val + b.val := by decide
  rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ => h (x i) (y i)

theorem inter_cast (x y : Fin 8 → ZMod 2) :
    ((∑ i, (x i * y i).val : ℕ) : ZMod 2) = x ⬝ᵥ y := by
  simp [dotProduct]

theorem qP_add {x y : Fin 8 → ZMod 2} (hx : x ∈ permCore 8) (hy : y ∈ permCore 8) :
    qP (x + y) = qP x + qP y + x ⬝ᵥ y := by
  have hxy : x + y ∈ permCore 8 := (permCore 8).add_mem hx hy
  obtain ⟨a, ha⟩ := two_dvd_wt hx
  obtain ⟨b, hb⟩ := two_dvd_wt hy
  obtain ⟨c, hc⟩ := two_dvd_wt hxy
  have h := wt_add_inter x y
  rw [ha, hb, hc] at h
  have hnat : c + ∑ i, (x i * y i).val = a + b := by omega
  have hcast : (c : ZMod 2) + ((∑ i, (x i * y i).val : ℕ) : ZMod 2) = a + b := by
    exact_mod_cast congrArg (Nat.cast : ℕ → ZMod 2) hnat
  rw [inter_cast] at hcast
  have h2 : ∀ t : ZMod 2, t + t = 0 := by decide
  have e : ∀ n : ℕ, 2 * n / 2 = n := fun n => by omega
  unfold qP
  rw [hc, ha, hb, e, e, e]
  calc (c : ZMod 2) = (c + x ⬝ᵥ y) + x ⬝ᵥ y := by rw [add_assoc, h2, add_zero]
    _ = a + b + x ⬝ᵥ y := by rw [hcast]

theorem qP_zero : qP 0 = 0 := by
  decide

theorem qP_ones : qP ones8 = 0 := by
  decide

theorem qP_add_ones {x : Fin 8 → ZMod 2} (hx : x ∈ permCore 8) : qP (x + ones8) = qP x := by
  have h1 : ones8 ∈ permCore 8 := by
    show ∑ i, ones8 i = 0
    decide
  have h2 : ones8 ⬝ᵥ x = 0 := ones_dot hx
  rw [qP_add hx h1, qP_ones, dotProduct_comm, h2]
  simp

theorem qP_permAct (σ : Equiv.Perm (Fin 8)) (x : Fin 8 → ZMod 2) : qP (permAct σ x) = qP x := by
  unfold qP
  rw [wt_permAct]

variable {U : Type} [AddCommGroup U] [Module (ZMod 2) U] {H' : Subgroup (GLV U)}

namespace Data

variable (D : Data U H')

@[expose] noncomputable def q (u : U) : ZMod 2 := qP (D.sec u : Fin 8 → ZMod 2)

theorem q_β (x : ↥(permCore 8)) : D.q (D.β x) = qP x := by
  obtain ⟨z, hz, h⟩ := D.sec_β x
  unfold q
  rw [h]
  rcases hz with rfl | hz
  · simp
  · have hz' : (z : Fin 8 → ZMod 2) = ones8 := funext hz
    rw [Submodule.coe_add, hz']
    exact qP_add_ones x.2

theorem q_add (u v : U) : D.q (u + v) = D.q u + D.q v + D.B0 u v := by
  obtain ⟨x, rfl⟩ := D.surj u
  obtain ⟨y, rfl⟩ := D.surj v
  rw [← map_add, q_β, q_β, q_β, B0_β]
  exact qP_add x.2 y.2

theorem q_zero : D.q 0 = 0 := by
  unfold q
  rw [map_zero]
  exact qP_zero

theorem q_smul (c : ZMod 2) (u : U) : D.q (c • u) = c * c * D.q u := by
  have hc : ∀ c : ZMod 2, c = 0 ∨ c = 1 := by decide
  rcases hc c with rfl | rfl
  · rw [zero_smul, q_zero]
    simp
  · rw [one_smul]
    simp

theorem q_inv (γ : ↥H') (u : U) : D.q ((γ : GLV U) u) = D.q u := by
  obtain ⟨x, rfl⟩ := D.surj u
  rw [apply_β, q_β, q_β]
  exact qP_permAct _ _

theorem q_polar (u v : U) : D.q (u + v) - D.q u - D.q v = D.B0 u v := by
  rw [q_add]
  ring

theorem B0_nondegenerate : D.B0.Nondegenerate :=
  ⟨fun u hu => D.B0_left_sep u hu, fun v hv => D.B0_left_sep v (fun u => by
    rw [B0_symm]
    exact hv u)⟩

@[expose] def v3 (i : Fin 3) : Fin 8 → ZMod 2 :=
  ![![1, 1, 1, 1, 0, 0, 0, 0], ![1, 1, 0, 0, 1, 1, 0, 0], ![1, 0, 1, 0, 1, 0, 1, 0]] i

theorem v3_combo (a b c : ZMod 2) :
    ∑ i, (a • v3 0 + b • v3 1 + c • v3 2) i = 0 ∧ qP (a • v3 0 + b • v3 1 + c • v3 2) = 0 ∧
      ((a • v3 0 + b • v3 1 + c • v3 2 = 0 ∨
        a • v3 0 + b • v3 1 + c • v3 2 = ones8) → a = 0 ∧ b = 0 ∧ c = 0) := by
  revert a b c
  decide

end Data

end P3Ortho

end G11

end CFSG.Quasithin
