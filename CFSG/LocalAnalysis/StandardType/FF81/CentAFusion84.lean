module

public import CFSG.LocalAnalysis.StandardType.FF81.CentAFrame
import CFSG.LocalAnalysis.StandardType.FF81.CentAFrameAut
import CFSG.LocalAnalysis.StandardType.FF81.CentAModelInv
import CFSG.LocalAnalysis.StandardType.FF81.CentAModelTransv

public section

namespace CFSG.StandardType.FF81.CentA

open RootFusionLin

variable {G : Type} [Group G] [Finite G] {m : ℕ} {Y L R : Subgroup G} {b t : G}
  {φ : ↥Y ≃* GL (BlkIdx 1 m) (ZMod 2)}

theorem conj_mem_liftSub_uOne_or_uTwo (hS : CentASetting m Y L R b t φ)
    (hfus : CentAFus Y b t φ) {g : G} (hg : g * t * g⁻¹ ∈ liftSub φ (uSub 1 m)) :
    g * t * g⁻¹ ∈ liftSub φ (uOne m) ∨ g * t * g⁻¹ ∈ liftSub φ (uTwo m) := by
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 2 := by
    rcases hS.m_cases with h | h
    · exact ⟨4, by omega⟩
    · exact ⟨5, by omega⟩
  let H : Subgroup G := Subgroup.centralizer ({t} : Set G)
  obtain ⟨huY, huK⟩ := (mem_liftSub (φ := φ)).mp hg
  obtain ⟨a, b₁, c, huEq⟩ := (mem_uSub_iff (r := 1) (m := k + 2)).mp huK
  have htt : t * t = 1 := by
    have h : (⟨t, hS.t_mem⟩ : ↥Y) * ⟨t, hS.t_mem⟩ = 1 := by
      apply φ.injective
      rw [map_mul, map_one, hS.φ_t]
      exact jGL_mul_self (r := 1) (m := k + 2)
    simpa using congrArg (fun y : ↥Y => (y : G)) h
  have huu : (g * t * g⁻¹) * (g * t * g⁻¹) = 1 := by
    calc (g * t * g⁻¹) * (g * t * g⁻¹) = g * (t * t) * g⁻¹ := by group
      _ = 1 := by rw [htt]; group
  have h2 : uGL a b₁ c * uGL a b₁ c = 1 := by
    have hmem : (g * t * g⁻¹) * (g * t * g⁻¹) ∈ Y := Y.mul_mem huY huY
    have hφ : φ (⟨(g * t * g⁻¹) * (g * t * g⁻¹), hmem⟩ : ↥Y) =
        uGL a b₁ c * uGL a b₁ c := by
      rw [show (⟨(g * t * g⁻¹) * (g * t * g⁻¹), hmem⟩ : ↥Y) =
        ⟨g * t * g⁻¹, huY⟩ * ⟨g * t * g⁻¹, huY⟩ from rfl, map_mul, huEq]
    have hone : (⟨(g * t * g⁻¹) * (g * t * g⁻¹), hmem⟩ : ↥Y) = 1 := Subtype.ext huu
    rw [← hφ, hone, map_one]
  have hm : 4 ≤ k + 2 := by
    have h := hS.m_cases
    omega
  obtain ⟨R, hR⟩ := exists_levi_commute_bStar (m := k + 2) hm h2
  let y' : G := ((φ.symm (levi 1 R) : ↥Y) : G)
  have hy'Y : y' ∈ Y := (φ.symm (levi 1 R) : ↥Y).2
  have hy'φ : φ ⟨y', hy'Y⟩ = levi 1 R := by
    rw [show (⟨y', hy'Y⟩ : ↥Y) = φ.symm (levi 1 R) from Subtype.ext rfl]
    exact φ.apply_symm_apply _
  let b'' : G := y' * bStarG φ * y'⁻¹
  have hb''Y : b'' ∈ Y :=
    Y.mul_mem (Y.mul_mem hy'Y ((liftSub_le (φ := φ) (Cent 1 (k + 2))) (bStarG_mem hS).2))
      (Y.inv_mem hy'Y)
  have hb''φ : φ ⟨b'', hb''Y⟩ = levi 1 R * bStar (k + 2) * (levi 1 R)⁻¹ := by
    rw [show (⟨b'', hb''Y⟩ : ↥Y) = ⟨y', hy'Y⟩ * φ.symm (bStar (k + 2)) *
      ⟨y', hy'Y⟩⁻¹ from Subtype.ext rfl]
    rw [map_mul, map_mul, map_inv, hy'φ, φ.apply_symm_apply]
  have hcommu : b'' * (g * t * g⁻¹) = (g * t * g⁻¹) * b'' := by
    have h : (⟨b'', hb''Y⟩ : ↥Y) * ⟨g * t * g⁻¹, huY⟩ =
        ⟨g * t * g⁻¹, huY⟩ * ⟨b'', hb''Y⟩ := by
      apply φ.injective
      rw [map_mul, map_mul, hb''φ, huEq]
      exact hR.eq
    simpa using congrArg (fun y : ↥Y => (y : G)) h
  have hct : (g⁻¹ * b'' * g) * t = t * (g⁻¹ * b'' * g) := by
    calc (g⁻¹ * b'' * g) * t = g⁻¹ * (b'' * (g * t * g⁻¹)) * g := by group
      _ = g⁻¹ * ((g * t * g⁻¹) * b'') * g := by rw [hcommu]
      _ = t * (g⁻¹ * b'' * g) := by group
  let yπ : G := ((φ.symm (piStd k) : ↥Y) : G)
  let g₁ : G := g⁻¹ * y' * yπ
  have hc_eq : g⁻¹ * b'' * g = g₁ * b * g₁⁻¹ := by
    dsimp only [b'', g₁, y', yπ]
    rw [bStarG_eq_conj hS]
    group
  have hcH : g⁻¹ * b'' * g ∈ H := by
    show g⁻¹ * b'' * g ∈ Subgroup.centralizer ({t} : Set G)
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact hct
  have hg₁H : g₁ * b * g₁⁻¹ ∈ H := by
    rw [← hc_eq]
    exact hcH
  obtain ⟨h, hhH, hcase⟩ := hfus g₁ hg₁H
  let w : G := ((φ.symm (wStar (k + 2)) : ↥Y) : G)
  have hwY : w ∈ Y := (φ.symm (wStar (k + 2)) : ↥Y).2
  have hwmem : w ∈ liftSub φ (Cent 1 (k + 2)) := by
    refine liftSub_mono (φ := φ) (leviB_le_cent (k + 2)) ?_
    rw [mem_liftSub]
    refine ⟨hwY, ?_⟩
    rw [show (⟨w, hwY⟩ : ↥Y) = φ.symm (wStar (k + 2)) from Subtype.ext rfl]
    rw [φ.apply_symm_apply]
    exact wStar_mem_leviB (k + 2)
  have hwH : w ∈ H := by
    show w ∈ Subgroup.centralizer ({t} : Set G)
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact ((mem_liftSub_cent hS).mp hwmem).2
  have hwconj : w * (bStarG φ)⁻¹ * w⁻¹ = bStarG φ := by
    have hGL : wStar (k + 2) * (bStar (k + 2))⁻¹ * (wStar (k + 2))⁻¹ =
        bStar (k + 2) := by
      calc wStar (k + 2) * (bStar (k + 2))⁻¹ * (wStar (k + 2))⁻¹
          = (wStar (k + 2) * bStar (k + 2) * (wStar (k + 2))⁻¹)⁻¹ := by group
        _ = (bStar (k + 2))⁻¹⁻¹ := by rw [wStar_conj_bStar (k + 2)]
        _ = bStar (k + 2) := by group
    have hY : (φ.symm (wStar (k + 2)) : ↥Y) * (φ.symm (bStar (k + 2)) : ↥Y)⁻¹ *
        (φ.symm (wStar (k + 2)) : ↥Y)⁻¹ = (φ.symm (bStar (k + 2)) : ↥Y) := by
      apply φ.injective
      simpa only [map_mul, map_inv, MulEquiv.apply_symm_apply] using hGL
    have h := congrArg (fun y : ↥Y => (y : G)) hY
    simpa [w, bStarG] using h
  obtain ⟨h₂, hh₂H, hconj⟩ : ∃ h₂ ∈ H, h₂ * (g₁ * b * g₁⁻¹) * h₂⁻¹ = bStarG φ := by
    rcases hcase with hcase | hcase
    · exact ⟨h, hhH, hcase⟩
    · refine ⟨w * h, H.mul_mem hwH hhH, ?_⟩
      calc (w * h) * (g₁ * b * g₁⁻¹) * (w * h)⁻¹
          = w * (h * (g₁ * b * g₁⁻¹) * h⁻¹) * w⁻¹ := by group
        _ = w * (bStarG φ)⁻¹ * w⁻¹ := by
            rw [hcase]
            rfl
        _ = bStarG φ := hwconj
  let x : G := h₂ * g⁻¹ * y'
  have hxconj : x * bStarG φ * x⁻¹ = bStarG φ := by
    have hx1 : (h₂ * g⁻¹ * y') * bStarG φ * (h₂ * g⁻¹ * y')⁻¹ =
        h₂ * (g⁻¹ * b'' * g) * h₂⁻¹ := by
      dsimp only [b'']
      group
    dsimp only [x]
    rw [hx1, hc_eq, hconj]
  have hx : x ∈ Subgroup.centralizer ({bStarG φ} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc x * bStarG φ = (x * bStarG φ * x⁻¹) * x := by group
      _ = bStarG φ * x := by rw [hxconj]
  have hxinvN : x⁻¹ ∈ Subgroup.normalizer (lStar φ : Set G) :=
    centralizer_bStarG_le_normalizer hS ((Subgroup.centralizer ({bStarG φ} : Set G)).inv_mem hx)
  obtain ⟨y, hyY, hyconj⟩ := exists_conj_eq_of_mem_normalizer_lStar hS hxinvN
  have hyconj' : y * t * y⁻¹ = x⁻¹ * t * x := by
    simpa only [inv_inv] using hyconj
  have ht2 : h₂⁻¹ * t * h₂ = t := by
    have hcomm := Subgroup.mem_centralizer_singleton_iff.mp hh₂H
    calc h₂⁻¹ * t * h₂ = h₂⁻¹ * (t * h₂) := by group
      _ = h₂⁻¹ * (h₂ * t) := by rw [← hcomm]
      _ = t := by group
  have hxtx : x⁻¹ * t * x = y'⁻¹ * (g * t * g⁻¹) * y' := by
    calc x⁻¹ * t * x = y'⁻¹ * (g * (h₂⁻¹ * t * h₂) * g⁻¹) * y' := by
          dsimp only [x]
          group
      _ = y'⁻¹ * (g * t * g⁻¹) * y' := by rw [ht2]
  have hu_eq : y' * y * t * (y' * y)⁻¹ = g * t * g⁻¹ := by
    calc y' * y * t * (y' * y)⁻¹ = y' * (y * t * y⁻¹) * y'⁻¹ := by group
      _ = y' * (y'⁻¹ * (g * t * g⁻¹) * y') * y'⁻¹ := by rw [hyconj', hxtx]
      _ = g * t * g⁻¹ := by group
  have hIsConj : IsConj (jGL 1 (k + 2)) (uGL a b₁ c) := by
    have hmem : y' * y ∈ Y := Y.mul_mem hy'Y hyY
    have hYeq : (⟨y' * y, hmem⟩ : ↥Y) * ⟨t, hS.t_mem⟩ *
        (⟨y' * y, hmem⟩ : ↥Y)⁻¹ = ⟨g * t * g⁻¹, huY⟩ := Subtype.ext hu_eq
    have hφeq := congrArg φ hYeq
    rw [map_mul, map_mul, map_inv, hS.φ_t, huEq] at hφeq
    exact isConj_iff.mpr ⟨φ ⟨y' * y, hmem⟩, hφeq⟩
  rcases eq_zero_or_eq_zero_of_isConj hIsConj with ha | hb
  · exact Or.inr (mem_liftSub.mpr ⟨huY, by rw [huEq, ha]; exact ⟨b₁, c, rfl⟩⟩)
  · exact Or.inl (mem_liftSub.mpr ⟨huY, by rw [huEq, hb]; exact ⟨a, c, rfl⟩⟩)

theorem exists_conj_eq_of_mem_liftSub_uOne (hS : CentASetting m Y L R b t φ) {u : G}
    (hu : u ∈ liftSub φ (uOne m)) (h1 : u ≠ 1) : ∃ y ∈ Y, y * t * y⁻¹ = u := by
  obtain ⟨huY, huK⟩ := (mem_liftSub (φ := φ)).mp hu
  have hφu : φ ⟨u, huY⟩ ≠ 1 := by
    intro h
    apply h1
    have hueq : (⟨u, huY⟩ : ↥Y) = 1 := φ.injective (by rw [h, map_one])
    simpa using congrArg (fun y : ↥Y => (y : G)) hueq
  obtain ⟨c', hc'⟩ := isConj_iff.mp (isConj_of_mem_uOne huK hφu)
  refine ⟨((φ.symm c' : ↥Y) : G), (φ.symm c').2, ?_⟩
  have hsymm : φ.symm (jGL 1 m) = ⟨t, hS.t_mem⟩ := by
    apply φ.injective
    rw [MulEquiv.apply_symm_apply, hS.φ_t]
  have hYeq : (φ.symm c' : ↥Y) * (φ.symm (jGL 1 m) : ↥Y) * (φ.symm c' : ↥Y)⁻¹ =
      ⟨u, huY⟩ := by
    simpa only [map_mul, map_inv, MulEquiv.symm_apply_apply] using
      congrArg (fun z => φ.symm z) hc'
  have h := congrArg (fun y : ↥Y => (y : G)) hYeq
  rw [hsymm] at h
  simpa using h

theorem exists_conj_eq_of_mem_liftSub_uTwo (hS : CentASetting m Y L R b t φ) {u : G}
    (hu : u ∈ liftSub φ (uTwo m)) (h1 : u ≠ 1) : ∃ y ∈ Y, y * t * y⁻¹ = u := by
  obtain ⟨huY, huK⟩ := (mem_liftSub (φ := φ)).mp hu
  have hφu : φ ⟨u, huY⟩ ≠ 1 := by
    intro h
    apply h1
    have hueq : (⟨u, huY⟩ : ↥Y) = 1 := φ.injective (by rw [h, map_one])
    simpa using congrArg (fun y : ↥Y => (y : G)) hueq
  obtain ⟨c', hc'⟩ := isConj_iff.mp (isConj_of_mem_uTwo huK hφu)
  refine ⟨((φ.symm c' : ↥Y) : G), (φ.symm c').2, ?_⟩
  have hsymm : φ.symm (jGL 1 m) = ⟨t, hS.t_mem⟩ := by
    apply φ.injective
    rw [MulEquiv.apply_symm_apply, hS.φ_t]
  have hYeq : (φ.symm c' : ↥Y) * (φ.symm (jGL 1 m) : ↥Y) * (φ.symm c' : ↥Y)⁻¹ =
      ⟨u, huY⟩ := by
    simpa only [map_mul, map_inv, MulEquiv.symm_apply_apply] using
      congrArg (fun z => φ.symm z) hc'
  have h := congrArg (fun y : ↥Y => (y : G)) hYeq
  rw [hsymm] at h
  simpa using h

end CFSG.StandardType.FF81.CentA

end
