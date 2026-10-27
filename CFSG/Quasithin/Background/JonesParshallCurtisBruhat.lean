module

public import CFSG.Quasithin.Background.JonesParshallCurtisHecke
public import CFSG.Quasithin.Background.JonesParshallWords

public section

namespace CFSG.Quasithin.JonesParshall.Curtis

open Matrix

@[expose] def upWord : Fin 5 → Fin 5 → List (Fin 4) :=
  ![![[], [0], [0, 1, 0, 1], [0, 1, 2, 1, 0, 1, 2, 1], [0, 1, 2, 3, 2, 1, 0, 1, 2, 3, 2, 1]],
    ![[], [], [1], [1, 2, 1, 2], [1, 2, 3, 2, 1, 2, 3, 2]],
    ![[], [], [], [2], [2, 3, 2, 3]],
    ![[], [], [], [], [3]],
    ![[], [], [], [], []]]

theorem upWord_spec : ∀ i j : Fin 5, i < j →
    Matrix.transvection i j (1 : ZMod 2) = toMat (rootBM ((upWord i j).map (true, ·))) := by
  decide +kernel

theorem lower_transvection : ∀ i j : Fin 5, j < i →
    IsLoU (Matrix.transvection i j (1 : ZMod 2)) := by
  decide +kernel

theorem rootProd_true_mem (l : List (Fin 4)) :
    rootProd (l.map (true, ·)) ∈ Subgroup.closure ((Lgrp : Set G5) ∪ Set.range xE) := by
  induction l with
  | nil => exact Subgroup.one_mem _
  | cons s l ih =>
    rw [List.map_cons, rootProd_cons]
    exact Subgroup.mul_mem _ (Subgroup.subset_closure (Or.inr ⟨s, rfl⟩)) ih

theorem closure_gens
    : Subgroup.closure ((Lgrp : Set G5) ∪ Set.range xE) = ⊤ := by
  refine closure_eq_top_of_transvection fun t => ?_
  obtain ⟨i, j, hij, c⟩ := t
  rcases (by decide : ∀ c : ZMod 2, c = 0 ∨ c = 1) c with rfl | rfl
  · rw [TransvectionStruct.toSpecialLinearGroup_mk, SpecialLinearGroup.transvection_coeff_zero]
    exact Subgroup.one_mem _
  · rw [TransvectionStruct.toSpecialLinearGroup_mk]
    rcases lt_or_gt_of_ne hij with h | h
    · have e : SpecialLinearGroup.transvection hij (1 : ZMod 2) =
          rootProd ((upWord i j).map (true, ·)) :=
        Subtype.ext (by rw [rootProd_coe]; exact upWord_spec i j h)
      rw [e]
      exact rootProd_true_mem _
    · exact Subgroup.subset_closure (Or.inl (lower_transvection i j h))

@[expose] def IsCell (g : G5) : Prop := ∃ q ∈ Lgrp, ∃ k : Fin 120, ∃ u ∈ Ugrp, g = q * wE k * u

theorem cell_checks : ∀ s : Fin 4, xE s = yE s * sE s * yE s ∧ xE s * yE s = yE s * sE s := by
  decide +kernel

theorem Qm_sconj
    {s : Fin 4} {M : Matrix (Fin 5) (Fin 5) (ZMod 2)} (h : IsQm s M) :
    IsLoU (sM s * M * sM s) := by
  have h1 := Qm_conj_x (Qm_conj_y (Qm_conj_x h))
  have e : sM s * M * sM s = xM s * (yM s * (xM s * M * xM s) * yM s) * xM s := by
    change (xM s * yM s * xM s) * M * (xM s * yM s * xM s) = _
    simp only [mul_assoc]
  rw [e]
  exact h1.1

theorem xE_mul_cell
    (s : Fin 4) {g : G5} (hg : IsCell g) : IsCell (xE s * g) := by
  obtain ⟨q, hq, k, u, hu, rfl⟩ := hg
  obtain ⟨hxe, hxy⟩ := cell_checks s
  have hxx : xE s * xE s = 1 := xE_mul_self s
  have e0 : xE s * (q * wE k * u) = xE s * q * (xE s * xE s) * wE k * u := by
    rw [hxx, mul_one]
    group
  rcases decomp_lo (s := s) (show IsLoU (q : Matrix (Fin 5) (Fin 5) (ZMod 2)) from hq) with h | h
  ·
    have hq' : xE s * q * xE s ∈ Lgrp := (Qm_conj_x h).1
    rcases wE_conj k s with h1 | h1
    · refine ⟨xE s * q * xE s, hq', k, (wE k)⁻¹ * xE s * wE k * u, Ugrp.mul_mem h1 hu, ?_⟩
      rw [e0]
      group
    · refine ⟨xE s * q * xE s * yE s, Lgrp.mul_mem hq' (yE_mem s), mulTab s k,
        (wE k)⁻¹ * yE s * wE k * u, Ugrp.mul_mem h1 hu, ?_⟩
      rw [← sE_mul_wE]
      calc xE s * (q * wE k * u) = xE s * q * (xE s * xE s) * wE k * u := e0
        _ = xE s * q * xE s * (yE s * sE s * yE s) * wE k * u := by
            rw [← hxe]
            group
        _ = _ := by group
  ·
    set q₀ := yE s * q
    have hq0 : q = yE s * q₀ := by rw [← mul_assoc, yE_mul_self, one_mul]
    have hs : sE s * q₀ * sE s ∈ Lgrp := Qm_sconj h
    refine ⟨yE s * (sE s * q₀ * sE s), Lgrp.mul_mem (yE_mem s) hs, mulTab s k, u, hu, ?_⟩
    rw [← sE_mul_wE]
    calc xE s * (q * wE k * u) = (xE s * yE s) * q₀ * wE k * u := by
          rw [hq0]
          group
      _ = yE s * sE s * q₀ * wE k * u := by rw [hxy]
      _ = yE s * sE s * q₀ * (sE s * sE s) * wE k * u := by rw [sE_mul_self, mul_one]
      _ = _ := by group

theorem bruhat_cover
    (g : G5) : IsCell g := by
  have hg : g ∈ Subgroup.closure ((Lgrp : Set G5) ∪ Set.range xE) := by
    rw [closure_gens]
    exact Subgroup.mem_top g
  induction hg using Subgroup.closure_induction_left with
  | one => exact ⟨1, Lgrp.one_mem, 0, 1, Ugrp.one_mem, by rw [wE_zero]; group⟩
  | mul_left x hx y _ ih =>
    rcases hx with hx | ⟨s, rfl⟩
    · obtain ⟨q, hq, k, u, hu, rfl⟩ := ih
      exact ⟨x * q, Lgrp.mul_mem hx hq, k, u, hu, by group⟩
    · exact xE_mul_cell s ih
  | inv_mul_cancel x hx y _ ih =>
    rcases hx with hx | ⟨s, rfl⟩
    · obtain ⟨q, hq, k, u, hu, rfl⟩ := ih
      exact ⟨x⁻¹ * q, Lgrp.mul_mem (Lgrp.inv_mem hx) hq, k, u, hu, by group⟩
    · rw [xE_inv]
      exact xE_mul_cell s ih

end CFSG.Quasithin.JonesParshall.Curtis
