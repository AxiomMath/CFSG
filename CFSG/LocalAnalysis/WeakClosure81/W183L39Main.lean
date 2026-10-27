module

public import CFSG.LocalAnalysis.WeakClosure81.W183L39Case
import CFSG.SignalizerFunctorTheorem.Quadratic.Invariance

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.SignalizerFunctorTheorem.Quadratic CFSG.Quasithin.G11 CFSG.Open Subgroup

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]

theorem w183l39_exists_swapper_moving {Y T L₁ L₂ : Subgroup (LGL 2 V)}
    (htwo : Br2TwoComp Y T L₁ L₂) {D : Subgroup (LGL 2 V)} (hDY : D ≤ Y) {a d : LGL 2 V}
    (ha : a ∈ D) (hd : d ∈ D) (hswap : cj a L₁ = L₂) {v : V} (hdv : d v ≠ v) :
    ∃ s ∈ D, cj s L₁ = L₂ ∧ s v ≠ v := by
  by_cases hav : a v = v
  · rcases htwo.perm d (hDY hd) with ⟨hdL, -⟩ | ⟨hdL, -⟩
    · refine ⟨a * d, D.mul_mem ha hd, ?_, ?_⟩
      · rw [cj_mul, hdL, hswap]
      · intro h
        have h' : a (d v) = v := by
          rwa [LinearEquiv.mul_apply] at h
        have hdveq : d v = v := by
          have hcongr := congrArg (fun w => a.symm w) h'
          rw [LinearEquiv.symm_apply_apply] at hcongr
          have hsymm : a.symm v = v := (LinearEquiv.symm_apply_eq a).mpr hav.symm
          rw [hcongr, hsymm]
        exact hdv hdveq
    · exact ⟨d, hd, hdL, hdv⟩
  · exact ⟨a, ha, hswap, hav⟩

theorem w183l39_false_of_swap {Y T L₁ L₂ : Subgroup (LGL 2 V)} {Γ : Set (Subgroup (LGL 2 V))}
    {VA : Subgroup (LGL 2 V) → Submodule (ZMod 2) V} {i : ℕ}
    (h : Assumption131 Y Γ VA i) (htwo : Br2TwoComp Y T L₁ L₂)
    {D : Subgroup (LGL 2 V)} (hD : D ∈ Γ)
    (hoff : ∃ B : Subgroup (LGL 2 V), B ≤ D ∧ mOf D B ≤ i ∧ fixSub D ≠ fixSub B)
    (h4 : 4 ≤ Nat.card ↥D) {a : LGL 2 V} (ha : a ∈ D) (hswap : cj a L₁ = L₂) : False := by
  obtain ⟨B, hBD, hBi, hne⟩ := hoff
  have hDab := h.isElemAb D hD
  have hDY := h.le_G D hD
  have hfixBD : fixSub D ≤ fixSub B := fixSub_anti B D hBD
  have hlt : ¬ fixSub B ≤ fixSub D := by
    intro hle
    exact hne (le_antisymm hfixBD hle)
  have hv : ∃ v ∈ fixSub B, v ∉ fixSub D := by
    by_contra hcon
    apply hlt
    intro v hvB
    by_contra hvD
    exact hcon ⟨v, hvB, hvD⟩
  obtain ⟨v, hvB, hvD⟩ := hv
  have hd : ∃ d ∈ D, d v ≠ v := by
    by_contra hcon
    apply hvD
    rw [mem_fixSub]
    intro d hdD
    by_contra hdv
    exact hcon ⟨d, hdD, hdv⟩
  obtain ⟨d, hdD, hdv⟩ := hd
  obtain ⟨s, hsD, hsswap, hsv⟩ :=
    w183l39_exists_swapper_moving htwo hDY ha hdD hswap hdv
  have hsq : s * s = 1 := by
    have hs2 := hDab.2 s hsD
    rwa [pow_two] at hs2
  let c : W183L39.SwapCfg Y T L₁ L₂ s := ⟨htwo, hDY hsD, hsq, hsswap⟩
  have h3 : 2 < Nat.card ↥D := by omega
  obtain ⟨b, hbD, hb1, hbL⟩ := W183L39.exists_inner c hDab hDY hsD h3
  exact W183L39.false_of_good h c hD hsD hbD hb1 hbL hBD hBi hvB hsv

theorem w183l39_false_of_swap_common {Y T L₁ L₂ : Subgroup (LGL 2 V)}
    {Γ : Set (Subgroup (LGL 2 V))} {VA : Subgroup (LGL 2 V) → Submodule (ZMod 2) V}
    {𝒢 : Set (Subgroup (LGL 2 V))} {Zs : Submodule (ZMod 2) V} {m i₀ : ℕ}
    {δ : Subgroup (LGL 2 V) → ℕ} (hc : Br2Common Y Γ VA T 𝒢 Zs m i₀ δ)
    (htwo : Br2TwoComp Y T L₁ L₂) {D : Subgroup (LGL 2 V)} (hD : D ∈ Γ)
    (h4 : 4 ≤ Nat.card ↥D) {a : LGL 2 V} (ha : a ∈ D) (hswap : cj a L₁ = L₂) : False := by
  obtain ⟨B, hBD, hB2, hne⟩ := hc.noOffender D hD
  exact w183l39_false_of_swap hc.h131 htwo hD
    ⟨B, hBD, hB2.trans (by have := hc.hmi; omega), hne⟩ h4 ha hswap

end CFSG.LocalAnalysis.WeakClosure81

end
