module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveWeylE6QTwoOmegaRootsD4Aux

public section

namespace CFSG.StandardType.E6QTwo

open Module CFSG.Assembly
open scoped Matrix

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [Finite V]
  {B : LinearMap.BilinForm (ZMod 3) V}

theorem phiD_facts_of_frame (hV : Nat.card V = 3 ^ 5) {f : Fin 5 → V}
    (hf : ∀ i j, B (f i) (f j) = if i = j then 1 else 0) {x y : V} (hf0 : f 0 = x)
    (hyx : ∀ a : ZMod 3, y ≠ a • x)
    (h12 : 12 ≤ Set.ncard {v : V | B v v = 2 ∧ B v x = 0 ∧ B v y = 0}) :
    Set.ncard {v : V | B v v = 2 ∧ B v x = 0 ∧ B v y = 0} = 12 ∧
      (∀ u : V, (∀ v : V, B v v = 2 → B v x = 0 → B v y = 0 → B v u = 0) →
        ∃ a b : ZMod 3, u = a • x + b • y) ∧
      (∀ v : V, B v v = 2 → B v x = 0 → B v y = 0 →
        ∃ w : V, B w w = 2 ∧ B w x = 0 ∧ B w y = 0 ∧ w ≠ v ∧ w ≠ -v ∧ B v w ≠ 0) ∧
      ∀ a b : ZMod 3, b ≠ 0 →
        (B x (a • x + b • y) ≠ 0 ∧ B (a • x + b • y) (a • x + b • y) = 2) ∨
          (B x (a • x + b • y) = 0 ∧ B (a • x + b • y) (a • x + b • y) = 1) := by
  classical
  let F : V ≃ₗ[ZMod 3] (Fin 5 → ZMod 3) := frameCoord hV hf
  let c : Fin 5 → ZMod 3 := F y
  let Φ : Set V := {v : V | B v v = 2 ∧ B v x = 0 ∧ B v y = 0}
  have hx0 : F x = stdE0 := by
    change frameCoord hV hf x = stdE0
    rw [← hf0, frameCoord_frame hV hf 0]
    rfl
  have hBv (v : V) : B v v = F v ⬝ᵥ F v := frameCoord_form hV hf v v
  have hBx (v : V) : B v x = F v 0 := by
    have h := frameCoord_apply hV hf v 0
    rw [hf0] at h
    exact h.symm
  have hBx' (v : V) : B x v = F v 0 := by
    rw [frameCoord_form hV hf x v, hx0]
    exact single_one_dotProduct (i := 0) (v := F v)
  have hBy (v : V) : B v y = F v ⬝ᵥ c := by
    have h := frameCoord_form hV hf v y
    simpa only [c] using h
  have himage : F '' Φ = (stdPhi c : Set (Fin 5 → ZMod 3)) := by
    ext u
    constructor
    · rintro ⟨v, hv, rfl⟩
      change B v v = 2 ∧ B v x = 0 ∧ B v y = 0 at hv
      simp only [stdPhi, Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨by rw [← hBv v]; exact hv.1, by rw [← hBx v]; exact hv.2.1,
        by rw [← hBy v]; exact hv.2.2⟩
    · intro hu
      simp only [stdPhi, Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hu
      refine ⟨F.symm u, ?_, F.apply_symm_apply u⟩
      change B (F.symm u) (F.symm u) = 2 ∧ B (F.symm u) x = 0 ∧ B (F.symm u) y = 0
      exact ⟨by rw [hBv, F.apply_symm_apply]; exact hu.1,
        by rw [hBx, F.apply_symm_apply]; exact hu.2.1,
        by rw [hBy, F.apply_symm_apply]; exact hu.2.2⟩
  have hcard : Φ.ncard = (stdPhi c).card := by
    rw [← Set.ncard_image_of_injective (f := F) Φ F.injective, himage, Set.ncard_coe_finset]
  have h12' : 12 ≤ (stdPhi c).card := by
    rw [← hcard]
    exact h12
  have hc : stdGood c := by
    by_contra h
    push Not at h
    obtain ⟨h1, h2, h3, h4⟩ := h
    have hc_eq : c = c 0 • stdE0 := by
      funext i
      fin_cases i <;> simp [stdE0, h1, h2, h3, h4]
    have hsymm : F.symm stdE0 = x := by
      rw [← hx0, F.symm_apply_apply]
    have hy_eq : y = c 0 • x := by
      calc y = F.symm (F y) := (F.symm_apply_apply y).symm
        _ = F.symm c := rfl
        _ = F.symm (c 0 • stdE0) := congrArg F.symm hc_eq
        _ = c 0 • F.symm stdE0 := by rw [map_smul]
        _ = c 0 • x := by rw [hsymm]
    exact hyx (c 0) hy_eq
  have hcset : c ∈ stdGoodSet := mem_stdGoodSet c hc h12'
  have hcard12 : (stdPhi c).card = 12 := stdPhi_card_set c hcset
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hcard, hcard12]
  · intro u hu
    have hu' : ∀ r ∈ stdPhi c, r ⬝ᵥ F u = 0 := by
      intro r hr
      have hr' : r ∈ (F '' Φ : Set (Fin 5 → ZMod 3)) := by
        rw [himage]
        exact hr
      obtain ⟨v, hv, hvr⟩ := hr'
      rw [← hvr, ← frameCoord_form hV hf v u]
      exact hu v hv.1 hv.2.1 hv.2.2
    obtain ⟨a, b, hab⟩ := stdPhi_perp_set c hcset (F u) hu'
    refine ⟨a, b, ?_⟩
    apply F.injective
    rw [map_add, map_smul, map_smul, hx0]
    change F u = a • stdE0 + b • c
    exact hab
  · intro v hv hvx hvy
    have hr : F v ∈ stdPhi c := by
      simp only [stdPhi, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨by rw [← hBv v]; exact hv, by rw [← hBx v]; exact hvx,
        by rw [← hBy v]; exact hvy⟩
    obtain ⟨w', hw', hne1, hrest⟩ := stdPhi_third_set c hcset (F v) hr
    obtain ⟨hne2, hdot⟩ := hrest
    have hw'P : w' ⬝ᵥ w' = 2 ∧ w' 0 = 0 ∧ w' ⬝ᵥ c = 0 := by
      simpa only [stdPhi, Finset.mem_filter, Finset.mem_univ, true_and] using hw'
    obtain ⟨hw'1, hw'2, hw'3⟩ := hw'P
    refine ⟨F.symm w', ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hBv, F.apply_symm_apply]
      exact hw'1
    · rw [hBx, F.apply_symm_apply]
      exact hw'2
    · rw [hBy, F.apply_symm_apply]
      exact hw'3
    · intro h_eq
      apply hne1
      have := congrArg F h_eq
      simpa using this
    · intro h_eq
      apply hne2
      have h := congrArg F h_eq
      rw [map_neg] at h
      simpa using h
    · rw [frameCoord_form hV hf v (F.symm w'), F.apply_symm_apply]
      exact hdot
  · intro a b hb
    set d : V := a • x + b • y with hd
    have hFd : F d = a • stdE0 + b • c := by
      rw [hd, map_add, map_smul, map_smul, hx0]
    have hcoord := stdPhi_line_set c hcset a b hb
    rw [← hFd] at hcoord
    rw [← hBx' d, ← frameCoord_form hV hf d d] at hcoord
    exact hcoord

end CFSG.StandardType.E6QTwo

end
