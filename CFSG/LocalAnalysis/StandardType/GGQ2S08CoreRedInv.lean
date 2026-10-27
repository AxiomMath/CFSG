module

public import CFSG.LocalAnalysis.StandardType.GGQ2S08CoreDefs

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

theorem ggQ2s08core_red_invariant {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    (H : Submodule (ZMod 3) V) (xv : V) (hH : IsCompl H (Submodule.span (ZMod 3) {xv}))
    (W R : Subgroup (V ≃ₗ[ZMod 3] V)) (hWR : W ≤ R) (hWH : ∀ w ∈ W, ∀ h ∈ H, w h ∈ H)
    (hWfix : ∀ v, (∀ w ∈ W, w v = v) ↔ v ∈ Submodule.span (ZMod 3) {xv})
    (hWirrH : ∀ U : Submodule (ZMod 3) V, U ≤ H → (∀ w ∈ W, ∀ u ∈ U, w u ∈ U) → U = ⊥ ∨ U = H)
    (r : V ≃ₗ[ZMod 3] V) (hrR : r ∈ R) (hrx : ¬ ∃ c : ZMod 3, r xv = c • xv)
    (U : Submodule (ZMod 3) V) (hU0 : U ≠ ⊥) (hU1 : U ≠ ⊤) (hUR : ∀ a ∈ R, ∀ u ∈ U, a u ∈ U) :
    U = H := by
  let L : Submodule (ZMod 3) V := Submodule.span (ZMod 3) {xv}
  have hHL : IsCompl H L := hH
  have hsup : H ⊔ L = ⊤ := hHL.sup_eq_top
  have hinf : H ⊓ L = ⊥ := hHL.inf_eq_bot
  have hUHW : ∀ w ∈ W, ∀ u ∈ U ⊓ H, w u ∈ U ⊓ H := by
    intro w hw u hu
    obtain ⟨huU, huH⟩ := Submodule.mem_inf.mp hu
    exact Submodule.mem_inf.mpr ⟨hUR w (hWR hw) u huU, hWH w hw u huH⟩
  rcases hWirrH (U ⊓ H) inf_le_right hUHW with hcase | hcase
  ·
    exfalso
    have hUL : U ≤ L := by
      intro u hu
      have hu_sup : u ∈ H ⊔ L := by rw [hsup]; exact Submodule.mem_top
      obtain ⟨h, hh, z, hz, hhz⟩ := Submodule.mem_sup.mp hu_sup
      obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hz
      have hWh : ∀ w ∈ W, w h = h := by
        intro w hw
        have hwu : w u ∈ U := hUR w (hWR hw) u hu
        have hwhH : w h ∈ H := hWH w hw h hh
        have hwx : w xv = xv :=
          (hWfix xv).mpr (Submodule.mem_span_singleton_self xv) w hw
        have hwu_eq : w u = w h + c • xv := by
          rw [← hhz, map_add, ← hc, map_smul, hwx]
        have hmem : w h - h ∈ U ⊓ H := by
          refine Submodule.mem_inf.mpr ⟨?_, H.sub_mem hwhH hh⟩
          have heq : w h - h = w u - u := by
            rw [hwu_eq, ← hhz, ← hc]
            abel
          rw [heq]
          exact U.sub_mem hwu hu
        have hbot : w h - h ∈ (⊥ : Submodule (ZMod 3) V) := by
          rw [← hcase]
          exact hmem
        exact sub_eq_zero.mp ((Submodule.mem_bot (ZMod 3)).mp hbot)
      have hhL : h ∈ L := (hWfix h).mp hWh
      have hh0 : h = 0 := by
        have hbot : h ∈ (⊥ : Submodule (ZMod 3) V) := by
          rw [← hinf]
          exact Submodule.mem_inf.mpr ⟨hh, hhL⟩
        exact (Submodule.mem_bot (ZMod 3)).mp hbot
      have hueq : u = c • xv := by
        rw [← hhz, ← hc, hh0, zero_add]
      exact Submodule.mem_span_singleton.mpr ⟨c, hueq.symm⟩
    obtain ⟨u, huU, hu0⟩ := (Submodule.ne_bot_iff U).mp hU0
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp (hUL huU)
    have hc0 : c ≠ 0 := by
      intro hc0
      apply hu0
      rw [← hc, hc0, zero_smul]
    have hxvU : xv ∈ U := by
      have hcu : c • xv ∈ U := by rw [hc]; exact huU
      have hsmul := U.smul_mem c⁻¹ hcu
      rwa [smul_smul, inv_mul_cancel₀ hc0, one_smul] at hsmul
    have hLU : L ≤ U := (Submodule.span_singleton_le_iff_mem xv U).mpr hxvU
    have hrxL : r xv ∈ L := hUL (hUR r hrR xv hxvU)
    obtain ⟨d, hd⟩ := Submodule.mem_span_singleton.mp hrxL
    exact hrx ⟨d, hd.symm⟩
  ·
    have hHU : H ≤ U := by rw [← hcase]; exact inf_le_left
    have hUH : U ≤ H := by
      intro u hu
      have hu_sup : u ∈ H ⊔ L := by rw [hsup]; exact Submodule.mem_top
      obtain ⟨h, hh, z, hz, hhz⟩ := Submodule.mem_sup.mp hu_sup
      obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hz
      have hsub : u - h = c • xv := by
        rw [← hhz, ← hc]
        abel
      have hcU : c • xv ∈ U := by rw [← hsub]; exact U.sub_mem hu (hHU hh)
      by_cases hc0 : c = 0
      · rw [← hhz, ← hc, hc0, zero_smul, add_zero]
        exact hh
      · exfalso
        have hxvU : xv ∈ U := by
          have hsmul := U.smul_mem c⁻¹ hcU
          rwa [smul_smul, inv_mul_cancel₀ hc0, one_smul] at hsmul
        have hLU : L ≤ U := (Submodule.span_singleton_le_iff_mem xv U).mpr hxvU
        have htop : (⊤ : Submodule (ZMod 3) V) ≤ U := by
          rw [← hsup]
          exact sup_le hHU hLU
        exact hU1 (eq_top_iff.mpr htop)
    exact le_antisymm hUH hHU

end CFSG.StandardType

end
