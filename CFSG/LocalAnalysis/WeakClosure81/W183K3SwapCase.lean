module

public import CFSG.LocalAnalysis.WeakClosure81.W183K3SwapFix
import CFSG.LocalAnalysis.WeakClosure81.W183Abs1
import CFSG.SignalizerFunctorTheorem.Quadratic.Invariance

public section

namespace CFSG.LocalAnalysis.WeakClosure81

namespace W183K3Swap

open CFSG.SignalizerFunctorTheorem.Quadratic CFSG.Quasithin.G11 CFSG.Open Subgroup W183K3

open scoped commutatorElement

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
variable {Y T L₁ L₂ : Subgroup (LGL 2 V)} {a : LGL 2 V}
variable {Γ : Set (Subgroup (LGL 2 V))} {VA : Subgroup (LGL 2 V) → Submodule (ZMod 2) V} {i : ℕ}

theorem false_of_zeta_normalizes (c : SwapCfg Y T L₁ L₂ a) {D : Subgroup (LGL 2 V)}
    (hD : IsElemAbelian 2 D) (hDY : D ≤ Y) (haD : a ∈ D) {b : LGL 2 V} (hbD : b ∈ D)
    (hb1 : b ≠ 1) (hbL : cj b L₁ = L₁)
    (hN : ∀ l ∈ L₁, zeta a l ∈ Subgroup.normalizer (D : Set (LGL 2 V))) : False := by
  have hba : b * a = a * b := IsElemAbelian.comm hD hbD haD
  have hbb : b * b = 1 := by
    have h2 := hD.2 b hbD
    rwa [pow_two] at h2
  let N : Subgroup ↥L₁ :=
    { carrier := {l | zeta a (l : LGL 2 V) ∈ D}
      one_mem' := by
        change zeta a (1 : LGL 2 V) ∈ D
        rw [zeta_one]
        exact D.one_mem
      mul_mem' := by
        intro l l' hl hl'
        change zeta a ((l : LGL 2 V) * (l' : LGL 2 V)) ∈ D
        rw [zeta_mul c l.2 l'.2]
        exact D.mul_mem hl hl'
      inv_mem' := by
        intro l hl
        change zeta a ((l : LGL 2 V))⁻¹ ∈ D
        rw [zeta_inv c l.2]
        exact D.inv_mem hl }
  haveI hNnormal : N.Normal :=
    ⟨fun n hn g => by
      change zeta a ((g : LGL 2 V) * (n : LGL 2 V) * (g : LGL 2 V)⁻¹) ∈ D
      rw [show zeta a ((g : LGL 2 V) * (n : LGL 2 V) * (g : LGL 2 V)⁻¹)
          = zeta a (g : LGL 2 V) * zeta a (n : LGL 2 V) * (zeta a (g : LGL 2 V))⁻¹ by
        rw [zeta_mul c (L₁.mul_mem g.2 n.2) (L₁.inv_mem g.2), zeta_mul c g.2 n.2,
          zeta_inv c g.2]]
      exact ((Subgroup.mem_set_normalizer_iff.mp (hN g g.2)
        (zeta a (n : LGL 2 V))).mp hn)⟩
  have hmem₁L : ∀ l ∈ L₁, b * l * b⁻¹ ∈ L₁ := by
    intro l hl
    have hcj : b * l * b⁻¹ ∈ cj b L₁ := by
      rw [mem_cj]
      have : b⁻¹ * (b * l * b⁻¹) * b = l := by group
      rwa [this]
    rwa [hbL] at hcj
  have hKn : ∀ y ∈ L₁, ∀ k ∈ N.map L₁.subtype, y * k * y⁻¹ ∈ N.map L₁.subtype := by
    intro y hy k hk
    obtain ⟨k₀, hk₀, hk₀eq⟩ := Subgroup.mem_map.mp hk
    rw [← hk₀eq]
    simpa using Subgroup.mem_map_of_mem L₁.subtype (hNnormal.conj_mem k₀ hk₀ ⟨y, hy⟩)
  rcases quasi_normal_dichotomy c.two.quasi₁ (Subgroup.map_subtype_le N) hKn with hZ | htop
  · refine hb1 (eq_one_of_comm_zeta c (hDY hbD) hba hbb hbL ?_)
    have hmemZ : ∀ l ∈ L₁, b * l * b⁻¹ * l⁻¹ ∈ quasiCentre L₁ := by
      intro l hl
      have hbl1L : b * l⁻¹ * b⁻¹ ∈ L₁ := hmem₁L l⁻¹ (L₁.inv_mem hl)
      have hz : zeta a (l * (b * l⁻¹ * b⁻¹)) ∈ D := by
        rw [zeta_mul c hl hbl1L]
        rw [show zeta a (b * l⁻¹ * b⁻¹) = b * (zeta a l)⁻¹ * b⁻¹ by
          rw [← zeta_conj (b := b) hba (l⁻¹), zeta_inv c hl]]
        have hzn : zeta a l ∈ Subgroup.normalizer (D : Set (LGL 2 V)) := hN l hl
        have hconj : zeta a l * b * (zeta a l)⁻¹ ∈ D :=
          ((Subgroup.mem_set_normalizer_iff.mp hzn) b).mp hbD
        have heq : zeta a l * (b * (zeta a l)⁻¹ * b⁻¹)
            = (zeta a l * b * (zeta a l)⁻¹) * b⁻¹ := by group
        rw [heq]
        exact D.mul_mem hconj (D.inv_mem hbD)
      have hmN : (⟨l * (b * l⁻¹ * b⁻¹), L₁.mul_mem hl hbl1L⟩ : ↥L₁) ∈ N := hz
      have hmem : l * (b * l⁻¹ * b⁻¹) ∈ N.map L₁.subtype :=
        Subgroup.mem_map_of_mem L₁.subtype hmN
      have hinv : (l * (b * l⁻¹ * b⁻¹))⁻¹ ∈ quasiCentre L₁ :=
        (quasiCentre L₁).inv_mem (hZ hmem)
      have heq : (l * (b * l⁻¹ * b⁻¹))⁻¹ = b * l * b⁻¹ * l⁻¹ := by group
      rwa [heq] at hinv
    have hcommL₁ : ∀ l ∈ L₁, b * l = l * b :=
      quasi_comm_of_comm_mod_centre c.two.quasi₁ hmem₁L hmemZ
    intro l hl
    have hbl : b * l * b⁻¹ = l := by rw [hcommL₁ l hl]; group
    have hconj : b * zeta a l * b⁻¹ = zeta a l := by rw [zeta_conj hba l, hbl]
    exact mul_inv_eq_iff_eq_mul.mp hconj
  · exfalso
    have hzD : ∀ l ∈ L₁, zeta a l ∈ D := by
      intro l hl
      have hmem : l ∈ N.map L₁.subtype := by rw [htop]; exact hl
      obtain ⟨k, hk, hkeq⟩ := Subgroup.mem_map.mp hmem
      rw [← hkeq]
      exact hk
    have hcomm : ⁅L₁, L₁⁆ ≤ quasiCentre L₁ := by
      rw [Subgroup.commutator_le]
      intro x hx y hy
      have hx' : x⁻¹ ∈ L₁ := L₁.inv_mem hx
      have hy' : y⁻¹ ∈ L₁ := L₁.inv_mem hy
      have hzx : zeta a x⁻¹ ∈ D := hzD x⁻¹ hx'
      have hzy : zeta a y⁻¹ ∈ D := hzD y⁻¹ hy'
      have hzxy : zeta a (x⁻¹ * y⁻¹) = zeta a (y⁻¹ * x⁻¹) := by
        rw [zeta_mul c hx' hy', zeta_mul c hy' hx', IsElemAbelian.comm hD hzx hzy]
      have hmem : (y⁻¹ * x⁻¹)⁻¹ * (x⁻¹ * y⁻¹) ∈ L₁ ⊓ L₂ :=
        zeta_eq_iff c (L₁.mul_mem hx' hy') (L₁.mul_mem hy' hx') hzxy
      have heq : ⁅x, y⁆ = (y⁻¹ * x⁻¹)⁻¹ * (x⁻¹ * y⁻¹) := by
        rw [commutatorElement_def]; group
      rw [heq]
      exact c.inf_le_centre hmem
    have habel : L₁ ≤ quasiCentre L₁ :=
      (le_of_eq (quasi_commutator_eq c.two.quasi₁).symm).trans hcomm
    obtain ⟨p, hp, q, hq, hpq⟩ := quasi_exists_noncomm c.two.quasi₁
    exact hpq ((mem_quasiCentre.mp (habel hp)).2 q hq)

theorem false_of_fixed_vector (h : Assumption131 Y Γ VA i) (c : SwapCfg Y T L₁ L₂ a)
    {D : Subgroup (LGL 2 V)} (hD : D ∈ Γ) (haD : a ∈ D) {b : LGL 2 V} (hbD : b ∈ D)
    (hb1 : b ≠ 1) (hbL : cj b L₁ = L₁) {J : V} (hJ : J ∈ VA D) (hJ0 : J ≠ 0)
    (hfix : ∀ l ∈ L₁, zeta a l J = J) : False := by
  exact false_of_zeta_normalizes c (h.isElemAb D hD) (h.le_G D hD) haD hbD hb1 hbL
    fun l hl => h.stabilizer_le_normalizer hD hJ hJ0 (zeta_mem_Y c hl) (hfix l hl)

theorem false_of_good (h : Assumption131 Y Γ VA i) (c : SwapCfg Y T L₁ L₂ a)
    {D : Subgroup (LGL 2 V)} (hD : D ∈ Γ) (haD : a ∈ D) {b : LGL 2 V} (hbD : b ∈ D)
    (hb1 : b ≠ 1) (hbL : cj b L₁ = L₁) {B : Subgroup (LGL 2 V)} (hBD : B ≤ D)
    (hBi : mOf D B ≤ i) {v : V} (hvB : v ∈ fixSub B) (hav : a v ≠ v) : False := by
  have hDab := h.isElemAb D hD
  have hba : b * a = a * b := IsElemAbelian.comm hDab hbD haD
  have hbb : b * b = 1 := by
    have h2 := hDab.2 b hbD
    rwa [pow_two] at h2
  have hJVA : a v - v ∈ VA D :=
    h.cond2 D hD B hBD hBi (sub_mem_commSpace (K := D) haD hvB)
  have hJ0 : a v - v ≠ 0 := sub_ne_zero.mpr hav
  let U : Set V := {u | ∃ w : V, u = a w - w}
  have hU : ∀ l ∈ L₁, ∀ u ∈ U, zeta a l u ∈ U := by
    intro l hl u hu
    obtain ⟨w, rfl⟩ := hu
    refine ⟨zeta a l w, ?_⟩
    have hcomm := congrArg (fun f : LGL 2 V => f w) (zeta_comm_a c hl)
    rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply] at hcomm
    simp only [map_sub, hcomm.symm]
  have hbU : ∀ u ∈ U, b u = u := by
    intro u hu
    obtain ⟨w, rfl⟩ := hu
    exact commSpace_eq_bot_iff.mp (h.quadratic D hD) b hbD (a w - w)
      (sub_mem_commSub D haD w)
  have hfixJ : ∀ l ∈ L₁, zeta a l (a v - v) = a v - v :=
    fun l hl => zeta_fixes_of_inner c (h.le_G D hD hbD) hba hbb hb1 hbL U hU hbU l hl
      (a v - v) ⟨v, rfl⟩
  exact false_of_fixed_vector h c hD haD hbD hb1 hbL hJVA hJ0 hfixJ

theorem w183k3_exists_swapper_moving (htwo : Br3TwoComp Y T L₁ L₂) {D : Subgroup (LGL 2 V)}
    (hDY : D ≤ Y) {a d : LGL 2 V} (ha : a ∈ D) (hd : d ∈ D) (hswap : cj a L₁ = L₂) {v : V}
    (hdv : d v ≠ v) : ∃ s ∈ D, cj s L₁ = L₂ ∧ s v ≠ v := by
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

theorem w183k3_false_of_diag_swap (h : Assumption131 Y Γ VA i) (htwo : Br3TwoComp Y T L₁ L₂)
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
    w183k3_exists_swapper_moving htwo hDY ha hdD hswap hdv
  have hsq : s * s = 1 := by
    have hs2 := hDab.2 s hsD
    rwa [pow_two] at hs2
  let c : SwapCfg Y T L₁ L₂ s := ⟨htwo, hDY hsD, hsq, hsswap⟩
  have h3 : 2 < Nat.card ↥D := by omega
  obtain ⟨b, hbD, hb1, hbL⟩ := exists_inner c hDab hDY hsD h3
  exact false_of_good h c hD hsD hbD hb1 hbL hBD hBi hvB hsv

end W183K3Swap

namespace W183K3

open CFSG.SignalizerFunctorTheorem.Quadratic CFSG.Quasithin.G11 CFSG.Open Subgroup

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]

theorem w183k3_false_of_swap_common {Y T L₁ L₂ : Subgroup (LGL 2 V)}
    {Γ : Set (Subgroup (LGL 2 V))} {VA : Subgroup (LGL 2 V) → Submodule (ZMod 2) V}
    {𝒢 : Set (Subgroup (LGL 2 V))} {Zs : Submodule (ZMod 2) V} {m i₀ : ℕ}
    {δ : Subgroup (LGL 2 V) → ℕ} (hc : Br2Common Y Γ VA T 𝒢 Zs m i₀ δ)
    (htwo : Br3TwoComp Y T L₁ L₂) {D : Subgroup (LGL 2 V)} (hD : D ∈ Γ)
    (h4 : 4 ≤ Nat.card ↥D) {a : LGL 2 V} (ha : a ∈ D) (hswap : cj a L₁ = L₂) : False := by
  obtain ⟨B, hBD, hB2, hne⟩ := hc.noOffender D hD
  exact W183K3Swap.w183k3_false_of_diag_swap hc.h131 htwo hD
    ⟨B, hBD, hB2.trans (by have := hc.hmi; omega), hne⟩ h4 ha hswap

end W183K3

end CFSG.LocalAnalysis.WeakClosure81

end
