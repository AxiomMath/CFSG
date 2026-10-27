module

public import CFSG.LocalAnalysis.WeakClosure81.Twelve

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.SignalizerFunctorTheorem.Quadratic CFSG.Quasithin.G11 CFSG.Open Subgroup

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]

private theorem b12_TwelveOddPart_add_self_eq_zero (x : V) : x + x = 0 := by
  have h := two_smul (ZMod 2) x
  rw [show (2 : ZMod 2) = 0 by decide, zero_smul] at h
  exact h.symm

private theorem b12_TwelveOddPart_exists_fixMod_aux (k : ℕ) :
    ∀ (w : LGL 2 V) (W S : Submodule (ZMod 2) V), W ≤ S → (∀ v ∈ W, w v ∈ W) →
      (∀ v ∈ S, w v ∈ S) → S ≠ W → w ^ 2 ^ k = 1 →
      ∃ s ∈ S, s ∉ W ∧ w s - s ∈ W := by
  induction k with
  | zero =>
      intro w W S hWS _hW _hS hne hk
      have hex : ∃ s ∈ S, s ∉ W := by
        by_contra h
        rw [not_exists] at h
        exact hne (le_antisymm (fun x hx => by
          by_contra hxW
          exact h x ⟨hx, hxW⟩) hWS)
      obtain ⟨s, hsS, hsW⟩ := hex
      refine ⟨s, hsS, hsW, ?_⟩
      rw [show w = 1 from by simpa using hk]
      simp
  | succ k ih =>
      intro w W S hWS hW hS hne hk
      have hk2 : (w ^ 2) ^ 2 ^ k = 1 := by
        rw [← pow_mul]
        rw [show 2 * 2 ^ k = 2 ^ (k + 1) from (pow_succ' 2 k).symm]
        exact hk
      have hW2 : ∀ v ∈ W, (w ^ 2) v ∈ W := by
        intro v hv
        rw [pow_two, LinearEquiv.mul_apply]
        exact hW (w v) (hW v hv)
      have hS2 : ∀ v ∈ S, (w ^ 2) v ∈ S := by
        intro v hv
        rw [pow_two, LinearEquiv.mul_apply]
        exact hS (w v) (hS v hv)
      obtain ⟨s, hsS, hsW, hs2⟩ := ih (w ^ 2) W S hWS hW2 hS2 hne hk2
      by_cases hws : w s - s ∈ W
      · exact ⟨s, hsS, hsW, hws⟩
      · refine ⟨w s - s, S.sub_mem (hS s hsS) hsS, hws, ?_⟩
        have key : w (w s - s) - (w s - s) =
            ((w ^ 2) s - s) - (w s + w s) + (s + s) := by
          rw [map_sub, pow_two, LinearEquiv.mul_apply]
          abel
        rw [key, b12_TwelveOddPart_add_self_eq_zero (w s),
          b12_TwelveOddPart_add_self_eq_zero s, sub_zero, add_zero]
        exact hs2

theorem exists_fixMod_of_two_element {w : LGL 2 V} (hw : ∃ k : ℕ, w ^ 2 ^ k = 1)
    {W S : Submodule (ZMod 2) V} (hWS : W ≤ S) (hW : ∀ v ∈ W, w v ∈ W)
    (hS : ∀ v ∈ S, w v ∈ S) (hne : S ≠ W) : ∃ s ∈ S, s ∉ W ∧ w s - s ∈ W := by
  obtain ⟨k, hk⟩ := hw
  exact b12_TwelveOddPart_exists_fixMod_aux k w W S hWS hW hS hne hk

theorem fixMod_inf_commSub_le_of_two_part {G : Subgroup (LGL 2 V)} {c w y : LGL 2 V}
    (hcG : c ∈ G) (hc : c = w * y) (hw : w ∈ Subgroup.zpowers c) (hy : y ∈ Subgroup.zpowers c)
    (hw2 : ∃ k : ℕ, w ^ 2 ^ k = 1) (hfix : fixMod (cE G) c ⊓ commSub G ≤ cE G) :
    fixMod (cE G) y ⊓ commSub G ≤ cE G := by
  have hwG : w ∈ G := Subgroup.zpowers_le.mpr hcG hw
  have hyG : y ∈ G := Subgroup.zpowers_le.mpr hcG hy
  obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp hw
  obtain ⟨l, hl⟩ := Subgroup.mem_zpowers_iff.mp hy
  have hwy : w * y = y * w := by
    rw [← hm, ← hl]
    exact (Commute.zpow_zpow_self c m l).eq
  have hyw : ∀ v : V, y (w v) = w (y v) := by
    intro v
    have h := congrArg (fun f : LGL 2 V => f v) hwy
    simp only [LinearEquiv.mul_apply] at h
    exact h.symm
  intro s hs
  by_contra hscE
  have hWS : cE G ≤ fixMod (cE G) y ⊓ commSub G := by
    intro v hv
    refine ⟨?_, cE_le_commSub G hv⟩
    show y v - v ∈ cE G
    exact (cE G).sub_mem (map_mem_cE G hyG hv) hv
  have hWinv : ∀ v ∈ cE G, w v ∈ cE G := fun v hv => map_mem_cE G hwG hv
  have hSinv : ∀ v ∈ fixMod (cE G) y ⊓ commSub G,
      w v ∈ fixMod (cE G) y ⊓ commSub G := by
    intro v hv
    refine ⟨?_, map_mem_commSub G hwG hv.2⟩
    show y (w v) - w v ∈ cE G
    have h2 : y (w v) - w v = w (y v - v) := by rw [hyw v, map_sub]
    rw [h2]
    exact map_mem_cE G hwG hv.1
  have hne : fixMod (cE G) y ⊓ commSub G ≠ cE G := by
    intro h
    rw [h] at hs
    exact hscE hs
  obtain ⟨t, htS, htW, htw⟩ :=
    exists_fixMod_of_two_element hw2 hWS hWinv hSinv hne
  have hcs : c t - t ∈ cE G := by
    have h2 : c t - t = (w t - t) + w (y t - t) := by
      rw [hc, LinearEquiv.mul_apply, map_sub]
      abel
    rw [h2]
    exact (cE G).add_mem htw (map_mem_cE G hwG htS.1)
  exact htW (hfix ⟨hcs, htS.2⟩)

theorem fixMod_inf_commSub_le_conj {G : Subgroup (LGL 2 V)} {y x : LGL 2 V} (hx : x ∈ G)
    (hfix : fixMod (cE G) y ⊓ commSub G ≤ cE G) :
    fixMod (cE G) (x⁻¹ * y * x) ⊓ commSub G ≤ cE G := by
  intro v hv
  have hxv : x v ∈ commSub G := map_mem_commSub G hx hv.2
  have hfixv : x v ∈ fixMod (cE G) y := by
    show y (x v) - x v ∈ cE G
    have h1 : y (x v) - x v = x ((x⁻¹ * y * x) v - v) := by
      rw [map_sub]
      rw [show (x⁻¹ * y * x) v = x⁻¹ (y (x v)) by simp only [LinearEquiv.mul_apply]]
      rw [apply_inv_apply']
    rw [h1]
    exact map_mem_cE G hx hv.1
  have hxcE : x v ∈ cE G := hfix ⟨hfixv, hxv⟩
  rw [show v = x⁻¹ (x v) from (inv_apply_apply' x v).symm]
  exact map_mem_cE G (G.inv_mem hx) hxcE

end CFSG.LocalAnalysis.WeakClosure81
