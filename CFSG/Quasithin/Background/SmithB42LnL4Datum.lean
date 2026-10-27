module

public import CFSG.Quasithin.Background.SmithB42LnL4Weyl
public import CFSG.Quasithin.Background.SmithCurtisMain

public section

namespace CFSG.Quasithin.B42Ln

open Matrix CFSG.Quasithin.SmithCurtis

local notation "𝕄₄" => Matrix (Fin 4) (Fin 4) (ZMod 2)

@[expose] def IsCell4 (g : G4) : Prop := ∃ l ∈ L4, ∃ w : W4, ∃ u ∈ U4, g = l * nW4 w * u

theorem nW4_conj_x4_or_y4 (w : W4) (s : Fin 3) :
    (nW4 w)⁻¹ * x4 s * nW4 w ∈ U4 ∨ (nW4 w)⁻¹ * y4 s * nW4 w ∈ U4 := by
  rw [nW4_apply, permHom_inv]
  exact pm_conj_x4_or_y4 (piW4 w) s

theorem x4_mul_cell (s : Fin 3) {g : G4} (hg : IsCell4 g) : IsCell4 (x4 s * g) := by
  obtain ⟨l, hl, w, u, hu, rfl⟩ := hg
  rcases L4_eq s hl with hq | hq
  · have hl' : x4 s * l * (x4 s)⁻¹ ∈ L4 := (x4_conj_Qs4 hq).1
    rcases nW4_conj_x4_or_y4 w s with h1 | h1
    · refine ⟨x4 s * l * (x4 s)⁻¹, hl', w, (nW4 w)⁻¹ * x4 s * nW4 w * u, U4.mul_mem h1 hu, ?_⟩
      group
    · refine ⟨x4 s * l * (x4 s)⁻¹ * y4 s, L4.mul_mem hl' (y4_mem s), cs4.simple s * w,
        (nW4 w)⁻¹ * y4 s * nW4 w * u, U4.mul_mem h1 hu, ?_⟩
      rw [map_mul, nW4_simple]
      calc x4 s * (l * nW4 w * u) = x4 s * l * (x4 s)⁻¹ * x4 s * nW4 w * u := by group
        _ = x4 s * l * (x4 s)⁻¹ * (y4 s * n4 s * y4 s) * nW4 w * u := by rw [← x4_eq]
        _ = _ := by group
  · obtain ⟨q, hq', rfl⟩ : ∃ q ∈ Qs4 s, l = y4 s * q :=
      ⟨y4 s * l, hq, by rw [← mul_assoc, y4_mul_self, one_mul]⟩
    refine ⟨y4 s * (n4 s * q * (n4 s)⁻¹), L4.mul_mem (y4_mem s) (n4_conj_Qs4 hq').1,
      cs4.simple s * w, u, hu, ?_⟩
    rw [map_mul, nW4_simple]
    calc x4 s * (y4 s * q * nW4 w * u) = (x4 s * y4 s) * q * nW4 w * u := by group
      _ = y4 s * n4 s * q * nW4 w * u := by rw [x4_mul_y4]
      _ = _ := by group

theorem bruhat_cover4 (g : G4) : IsCell4 g := by
  have hg : g ∈ Subgroup.closure ((L4 : Set G4) ∪ Set.range x4) := by
    rw [closure_L4_x4]
    exact Subgroup.mem_top g
  induction hg using Subgroup.closure_induction_left with
  | one => exact ⟨1, L4.one_mem, 1, 1, U4.one_mem, by rw [map_one]; group⟩
  | mul_left x hx y _ ih =>
    rcases hx with hx | ⟨s, rfl⟩
    · obtain ⟨l, hl, w, u, hu, rfl⟩ := ih
      exact ⟨x * l, L4.mul_mem hx hl, w, u, hu, by group⟩
    · exact x4_mul_cell s ih
  | inv_mul_cancel x hx y _ ih =>
    rcases hx with hx | ⟨s, rfl⟩
    · obtain ⟨l, hl, w, u, hu, rfl⟩ := ih
      exact ⟨x⁻¹ * l, L4.mul_mem (L4.inv_mem hx) hl, w, u, hu, by group⟩
    · rw [x4_inv]
      exact x4_mul_cell s ih

theorem mem_X4_cases {s : Fin 3} {x : G4} (hx : x ∈ X4 s) : x = 1 ∨ x = x4 s := hx

theorem mem_Y4_cases {s : Fin 3} {y : G4} (hy : y ∈ Y4 s) : y = 1 ∨ y = y4 s := hy

theorem X4_le (s : Fin 3) : X4 s ≤ U4 := by
  intro x hx
  rcases mem_X4_cases hx with rfl | rfl
  · exact U4.one_mem
  · exact x4_mem s

theorem Y4_le (s : Fin 3) : Y4 s ≤ L4 := by
  intro y hy
  rcases mem_Y4_cases hy with rfl | rfl
  · exact L4.one_mem
  · exact y4_mem s

@[expose] noncomputable def datum4 : CurtisDatum G4 cs4 2 where
  U := U4
  L := L4
  H := ⊥
  X := X4
  Y := Y4
  Us := Us4
  Q := Qs4
  n := n4
  nW := nW4
  isPGroup_U := isPGroup_U4
  isPGroup_L := isPGroup_L4
  U_inf_L := U4_inf_L4
  H_comm a ha b hb := by
    rw [Subgroup.mem_bot] at ha hb
    rw [ha, hb]
  H_normU h hh u hu := by
    rw [Subgroup.mem_bot.1 hh, one_mul, inv_one, mul_one]
    exact hu
  H_normU' h hh u hu := by
    rw [Subgroup.mem_bot.1 hh, inv_one, one_mul, mul_one]
    exact hu
  H_normL h hh l hl := by
    rw [Subgroup.mem_bot.1 hh, one_mul, inv_one, mul_one]
    exact hl
  H_normX s h hh x hx := by
    rw [Subgroup.mem_bot.1 hh, one_mul, inv_one, mul_one]
    exact hx
  H_normQ s h hh q hq := by
    rw [Subgroup.mem_bot.1 hh, one_mul, inv_one, mul_one]
    exact hq
  X_le := X4_le
  X_ne_bot s h := x4_ne_one s (by
    have hx : x4 s ∈ X4 s := Or.inr rfl
    rw [h] at hx
    exact hx)
  U_eq s u hu := U4_eq s hu
  Us_le s v hv := hv.1
  X_normUs s x hx v hv := conj_mem_Us4 (X4_le s hx) hv
  n_normUs s v hv := n4_conj_Us4 hv
  n_normUs' s v hv := by
    have h := n4_conj_Us4 hv
    rw [n4_inv] at h ⊢
    exact h
  Y_le := Y4_le
  Q_le s q hq := hq.1
  L_le s l hl := by
    rcases L4_eq s hl with h | h
    · exact Subgroup.mem_sup_right h
    · have e : l = y4 s * (y4 s * l) := by rw [← mul_assoc, y4_mul_self, one_mul]
      rw [e]
      exact Subgroup.mul_mem_sup (Or.inr rfl) h
  X_normQ s x hx q hq := by
    rcases mem_X4_cases hx with rfl | rfl
    · rw [one_mul, inv_one, mul_one]
      exact hq
    · exact x4_conj_Qs4 hq
  Y_normQ s y hy q hq := conj_mem_Qs4 (Y4_le s hy) hq
  n_normQ s q hq := n4_conj_Qs4 hq
  n_conjX s x hx := by
    rcases mem_X4_cases hx with rfl | rfl
    · exact Or.inl (by group)
    · exact Or.inr (n4_conj_x4 s)
  n_conjY s y hy := by
    rcases mem_Y4_cases hy with rfl | rfl
    · exact Or.inl (by group)
    · exact Or.inr (n4_conj_y4 s)
  n_sq s := Subgroup.mem_bot.2 (n4_mul_self s)
  n_normH s h hh := by
    rw [Subgroup.mem_bot] at hh ⊢
    rw [hh]
    group
  phi _ _ := 1
  psi _ _ := 1
  phi_mem _ _ _ _ := Subgroup.one_mem _
  psi_mem _ _ _ _ := Subgroup.one_mem _
  phi_spec s x hx hx1 := by
    rcases mem_X4_cases hx with rfl | rfl
    · exact absurd rfl hx1
    · exact ⟨y4 s, y4_mem s, x4 s, x4_mem s, by rw [mul_one, x4_mul_n4]⟩
  psi_spec s x hx hx1 := by
    rcases mem_X4_cases hx with rfl | rfl
    · exact absurd rfl hx1
    · exact ⟨x4 s, Or.inr rfl, x4 s, x4_mem s, by rw [mul_one]; exact n4_x4_n4 s⟩
  bruhatY s y hy hy1 := by
    rcases mem_Y4_cases hy with rfl | rfl
    · exact absurd rfl hy1
    · exact ⟨1, Subgroup.one_mem _, x4 s, Or.inr rfl, x4 s, Or.inr rfl, by
        rw [one_mul]
        exact y4_eq s⟩
  nW_one := map_one nW4
  nW_simple_mul w s _ := by rw [map_mul, nW4_simple]
  nW_conj w s h x hx := by
    rcases mem_X4_cases hx with rfl | rfl
    · rw [mul_one, inv_mul_cancel]
      exact U4.one_mem
    · exact nW4_conj_x4 h
  heckeDeg_mul w s h := heckeDeg_mul4 w s h
  cover g := by
    obtain ⟨l, hl, w, u, hu, rfl⟩ := bruhat_cover4 g
    exact ⟨l, hl, w, 1, Subgroup.one_mem _, u, hu, by rw [one_mul]⟩

theorem datum4_H : datum4.H = ⊥ := rfl

end CFSG.Quasithin.B42Ln
