module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC8CuClosure
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC8CuCoord
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC8CuWeyl

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.SpCurtis

open Matrix

@[expose] def IsCell (g : G6) : Prop := ∃ q ∈ Lgrp, ∃ k : Fin 48, ∃ u ∈ Ugrp, g = q * wE k * u

theorem Qm_sconj {s : Fin 3} {q : G6} (h : IsQm s (gM q)) : IsLoU (gM (sE s * q * sE s)) := by
  have h1 := Qm_conj_x (Qm_conj_y (Qm_conj_x h))
  have e : sE s * q * sE s = xE s * (yE s * (xE s * q * xE s) * yE s) * xE s := by
    rw [sE_def]
    simp only [mul_assoc]
  rw [e]
  exact h1.1

theorem xE_mul_cell (s : Fin 3) {g : G6} (hg : IsCell g) : IsCell (xE s * g) := by
  obtain ⟨q, hq, k, u, hu, rfl⟩ := hg
  have hxe : xE s = yE s * sE s * yE s := xE_eq_ysy s
  have hxy : xE s * yE s = yE s * sE s := xE_mul_yE s
  have hxx : xE s * xE s = 1 := xE_mul_self s
  have e0 : xE s * (q * wE k * u) = xE s * q * (xE s * xE s) * wE k * u := by
    rw [hxx, mul_one]
    group
  rcases decomp_lo (s := s) (show IsLoU (gM q) from hq) with h | h
  · have hq' : xE s * q * xE s ∈ Lgrp := (Qm_conj_x h).1
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
  · set q₀ := yE s * q
    have hq0 : q = yE s * q₀ := by rw [← mul_assoc, yE_mul_self, one_mul]
    have hs : sE s * q₀ * sE s ∈ Lgrp := Qm_sconj (q := q₀) h
    refine ⟨yE s * (sE s * q₀ * sE s), Lgrp.mul_mem (yE_mem s) hs, mulTab s k, u, hu, ?_⟩
    rw [← sE_mul_wE]
    calc xE s * (q * wE k * u) = (xE s * yE s) * q₀ * wE k * u := by
          rw [hq0]
          group
      _ = yE s * sE s * q₀ * wE k * u := by rw [hxy]
      _ = yE s * sE s * q₀ * (sE s * sE s) * wE k * u := by rw [sE_mul_self, mul_one]
      _ = _ := by group

theorem bruhat_cover (g : G6) : IsCell g := by
  have hg : g ∈ Subgroup.closure ((Lgrp : Set G6) ∪ Set.range xE) := by
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

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.SpCurtis
