module

public import CFSG.Quasithin.Background.G10FourSetup
import CFSG.Quasithin.Background.G10FourGL

public section

namespace CFSG.Quasithin

open CFSG.Quasithin.G11

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V]

theorem g10FourSplit_fix_span {y : GLV V} {S : Set V} (hS : ∀ s ∈ S, y s = s) {w : V}
    (hw : w ∈ Submodule.span (ZMod 2) S) : y w = w := by
  induction hw using Submodule.span_induction with
  | mem x hx => exact hS x hx
  | zero => exact map_zero y
  | add x z _ _ hx hz => rw [map_add, hx, hz]
  | smul c x _ hx => rw [map_smul, hx]

theorem g10FourSplit_fix_line {y : GLV V} {a : V} (hya : y a = a) {w : V}
    (hw : w ∈ Submodule.span (ZMod 2) {a}) : y w = w :=
  g10FourSplit_fix_span (fun s hs => by rw [Set.mem_singleton_iff.1 hs]; exact hya) hw

@[expose] def transGroup (H : Subgroup (GLV V)) (U : Submodule (ZMod 2) V) (hUH : Invariant H U)
    (a : V) : Subgroup (GLV V) where
  carrier := {y | y ∈ H ∧ y a = a ∧ ∀ u ∈ U, y u - u ∈ Submodule.span (ZMod 2) {a}}
  mul_mem' := by
    rintro y y' ⟨hy, hya, hyu⟩ ⟨hy', hy'a, hy'u⟩
    refine ⟨H.mul_mem hy hy', by rw [LinearEquiv.mul_apply, hy'a, hya], fun u hu => ?_⟩
    have h1 : (y * y') u - u = y (y' u - u) + (y u - u) := by
      rw [LinearEquiv.mul_apply, map_sub]
      abel
    rw [h1, g10FourSplit_fix_line hya (hy'u u hu)]
    exact Submodule.add_mem _ (hy'u u hu) (hyu u hu)
  one_mem' := ⟨H.one_mem, rfl, fun u _ => by simp⟩
  inv_mem' := by
    rintro y ⟨hy, hya, hyu⟩
    have hyinv : y⁻¹ ∈ H := H.inv_mem hy
    refine ⟨hyinv, ?_, fun u hu => ?_⟩
    · calc y⁻¹ a = y⁻¹ (y a) := by rw [hya]
        _ = a := by simp
    · have h1 := hyu (y⁻¹ u) (hUH y⁻¹ hyinv u hu)
      have h2 : y⁻¹ u - u = -(y (y⁻¹ u) - y⁻¹ u) := by simp
      rw [h2]
      exact Submodule.neg_mem _ h1

section TransGroup

variable {H : Subgroup (GLV V)} {U : Submodule (ZMod 2) V} (hUH : Invariant H U)

theorem transGroup_le (a : V) : transGroup H U hUH a ≤ H := fun _ hy => hy.1

theorem g10FourSplit_eq_one_of_faithful (hfaith : FaithfulOn H U) {k : GLV V} (hk : k ∈ H)
    (h : ∀ u ∈ U, k u = u) : k = 1 := by
  have : k ∈ centralizerOn H U := ⟨hk, h⟩
  rw [hfaith] at this
  exact Subgroup.mem_bot.1 this

theorem g10FourSplit_eq_of_faithful (hfaith : FaithfulOn H U) {k k' : GLV V} (hk : k ∈ H)
    (hk' : k' ∈ H) (h : ∀ u ∈ U, k u = k' u) : k = k' := by
  have := g10FourSplit_eq_one_of_faithful hfaith (H.mul_mem (H.inv_mem hk') hk)
    (fun u hu => by rw [LinearEquiv.mul_apply, h u hu]; simp)
  exact (inv_mul_eq_one.1 this).symm

theorem transGroup_mul_self (hfaith : FaithfulOn H U) {a : V} {y : GLV V}
    (hy : y ∈ transGroup H U hUH a) : y * y = 1 := by
  refine g10FourSplit_eq_one_of_faithful hfaith (H.mul_mem hy.1 hy.1) fun u hu => ?_
  have h1 := g10FourSplit_fix_line hy.2.1 (hy.2.2 u hu)
  rw [map_sub] at h1
  rw [LinearEquiv.mul_apply]
  have h2 : y (y u) = (y u - u) + y u := by rw [← h1]; abel
  rw [h2, sub_add_eq_add_sub, g10Four_add_self, zero_sub]
  exact neg_eq_of_add_eq_zero_left (g10Four_add_self u)

theorem transGroup_isPGroup (hfaith : FaithfulOn H U) (a : V) :
    IsPGroup 2 ↥(transGroup H U hUH a) := fun y => ⟨1, by
  rw [pow_one, pow_two]
  exact Subtype.ext (transGroup_mul_self hUH hfaith y.2)⟩

theorem conj_mem_transGroup {a : V} {y h : GLV V} (hh : h ∈ H)
    (hy : y ∈ transGroup H U hUH a) : h * y * h⁻¹ ∈ transGroup H U hUH (h a) := by
  obtain ⟨hyH, hya, hyu⟩ := hy
  refine ⟨H.mul_mem (H.mul_mem hh hyH) (H.inv_mem hh), ?_, fun u hu => ?_⟩
  · simp [hya]
  · have h1 := hyu (h⁻¹ u) (hUH h⁻¹ (H.inv_mem hh) u hu)
    have e : (h * y * h⁻¹) u - u = h (y (h⁻¹ u) - h⁻¹ u) := by simp
    rw [e]
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.1 h1
    rw [← hc, map_smul]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)

theorem exists_mem_transGroup (hall : AutAll H U) {a : U} (f : U →ₗ[ZMod 2] ZMod 2)
    (hfa : f a = 0) :
    ∃ y ∈ transGroup H U hUH (a : V), ∀ u : U, y (u : V) = (u : V) + f u • (a : V) := by
  obtain ⟨k, hkH, hk⟩ := hall (LinearEquiv.transvection hfa)
  have hk' : ∀ u : U, k (u : V) = (u : V) + f u • (a : V) := fun u => hk u
  refine ⟨k, ⟨hkH, by rw [hk' a, hfa, zero_smul, add_zero], fun u hu => ?_⟩, hk'⟩
  rw [hk' ⟨u, hu⟩, add_sub_cancel_left]
  exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)

theorem exists_form_of_mem_transGroup {y : GLV V} {a : U} (ha : a ≠ 0) (hya : y (a : V) = a)
    (hyu : ∀ u ∈ U, y u - u ∈ Submodule.span (ZMod 2) {(a : V)}) :
    ∃ f : U →ₗ[ZMod 2] ZMod 2, f a = 0 ∧ ∀ u : U, y (u : V) = (u : V) + f u • (a : V) := by
  have ha' : (a : V) ≠ 0 := fun h => ha (Subtype.ext h)
  let φ : U →ₗ[ZMod 2] V := ((y : V →ₗ[ZMod 2] V) - LinearMap.id) ∘ₗ U.subtype
  have hφ : ∀ u : U, φ u ∈ Submodule.span (ZMod 2) {(a : V)} := fun u => hyu u u.2
  let c := LinearEquiv.coord (ZMod 2) V (a : V) ha'
  refine ⟨c.toLinearMap ∘ₗ φ.codRestrict _ hφ, ?_, fun u => ?_⟩
  · have h0 : (⟨φ a, hφ a⟩ : Submodule.span (ZMod 2) {(a : V)}) = 0 :=
      Subtype.ext (by simp [φ, hya])
    show c ⟨φ a, hφ a⟩ = 0
    rw [h0, map_zero]
  · have h2 : c ⟨φ u, hφ u⟩ • (a : V) = y u - u :=
      LinearEquiv.coord_apply_smul (ZMod 2) V (a : V) ha' ⟨φ u, hφ u⟩
    show y u = u + c ⟨φ u, hφ u⟩ • (a : V)
    rw [h2]
    abel

end TransGroup

theorem g10FourSplit_odd_ncard_orbit {Γ H : Subgroup (GLV V)} {v₁ : V} (hHΓ : H ≤ Γ)
    (hHn : ∀ γ ∈ Γ, ∀ h ∈ H, γ * h * γ⁻¹ ∈ H)
    (hodd : Odd (MulAction.stabilizer Γ v₁).index) : Odd (MulAction.orbit H v₁).ncard := by
  classical
  let N : Subgroup ↥Γ := H.subgroupOf Γ
  have hN : N.Normal := ⟨fun n hn g => hHn g.1 g.2 n.1 hn⟩
  let a₀ : MulAction.orbit ↥Γ v₁ := ⟨v₁, MulAction.mem_orbit_self v₁⟩
  have hB := MulAction.IsBlock.orbit_of_normal (G := ↥Γ) (N := N) a₀
  have hdvd := hB.ncard_dvd_card ⟨a₀, MulAction.mem_orbit_self a₀⟩
  have hcard : Nat.card (MulAction.orbit ↥Γ v₁) = (MulAction.stabilizer Γ v₁).index := by
    rw [MulAction.index_stabilizer, Nat.card_coe_set_eq]
  have himg : Subtype.val '' (MulAction.orbit N a₀) = MulAction.orbit H v₁ := by
    ext t
    constructor
    · rintro ⟨x, ⟨n, rfl⟩, rfl⟩
      exact ⟨⟨n.1.1, n.2⟩, rfl⟩
    · rintro ⟨h, rfl⟩
      exact ⟨_, ⟨⟨⟨h.1, hHΓ h.2⟩, h.2⟩, rfl⟩, rfl⟩
  have hncard : (MulAction.orbit N a₀).ncard = (MulAction.orbit H v₁).ncard := by
    rw [← himg, Set.ncard_image_of_injective _ Subtype.val_injective]
  rw [← hncard]
  rw [hcard] at hdvd
  exact hodd.of_dvd_nat hdvd

theorem g10FourSplit_exists_fixed {Γ H P : Subgroup (GLV V)} {v₁ : V} (hHΓ : H ≤ Γ)
    (hHn : ∀ γ ∈ Γ, ∀ h ∈ H, γ * h * γ⁻¹ ∈ H)
    (hodd : Odd (MulAction.stabilizer Γ v₁).index) (hPH : P ≤ H) (hP : ∀ p ∈ P, p * p = 1) :
    ∃ h ∈ H, ∀ p ∈ P, p (h v₁) = h v₁ := by
  classical
  let P' : Subgroup ↥H := P.subgroupOf H
  have hP' : IsPGroup 2 ↥P' := fun g => ⟨1, by
    rw [pow_one, pow_two]
    exact Subtype.ext (Subtype.ext (hP g.1.1 g.2))⟩
  have hnd : ¬ 2 ∣ Nat.card (MulAction.orbit ↥H v₁) := by
    rw [Nat.card_coe_set_eq]
    exact fun hd => (Nat.not_even_iff_odd.2 (g10FourSplit_odd_ncard_orbit hHΓ hHn hodd))
      (even_iff_two_dvd.2 hd)
  obtain ⟨⟨t, ht⟩, hfix⟩ := hP'.nonempty_fixed_point_of_prime_not_dvd_card
    (MulAction.orbit ↥H v₁) hnd
  obtain ⟨h, rfl⟩ := ht
  refine ⟨h.1, h.2, fun p hp => ?_⟩
  have := hfix ⟨⟨p, hPH hp⟩, hp⟩
  exact congrArg Subtype.val this

section Step1

variable {H : Subgroup (GLV V)} {U : Submodule (ZMod 2) V} (hUH : Invariant H U)

theorem g10FourSplit_exists_conj_fix {Γ : Subgroup (GLV V)} {v₁ : V} (hHΓ : H ≤ Γ)
    (hHn : ∀ γ ∈ Γ, ∀ h ∈ H, γ * h * γ⁻¹ ∈ H) (hodd : Odd (MulAction.stabilizer Γ v₁).index)
    (hfaith : FaithfulOn H U) (a₀ : V) :
    ∃ h ∈ H, ∀ y ∈ transGroup H U hUH (h⁻¹ a₀), y v₁ = v₁ := by
  obtain ⟨h, hhH, hfix⟩ := g10FourSplit_exists_fixed hHΓ hHn hodd (transGroup_le hUH a₀)
    (fun p hp => transGroup_mul_self hUH hfaith hp)
  refine ⟨h, hhH, fun y hy => ?_⟩
  have h1 := conj_mem_transGroup hUH hhH hy
  have h2 : h (h⁻¹ a₀) = a₀ := by simp
  rw [h2] at h1
  have h4 : h (y v₁) = h v₁ := by simpa using hfix _ h1
  exact h.injective h4

theorem g10FourSplit_exists_notMem_span (hn : 2 ≤ Module.finrank (ZMod 2) U) {a : U} (ha : a ≠ 0) :
    ∃ s : U, s ∉ Submodule.span (ZMod 2) {a} := by
  have hspan : Module.finrank (ZMod 2) (Submodule.span (ZMod 2) {a}) = 1 :=
    finrank_span_singleton ha
  have hne : Submodule.span (ZMod 2) {a} ≠ ⊤ := by
    intro htop
    rw [htop, finrank_top] at hspan
    omega
  by_contra hcon
  push Not at hcon
  exact hne (eq_top_iff.2 fun s _ => hcon s)

theorem g10FourSplit_perp_of_fix {B : LinearMap.BilinForm (ZMod 2) V} {v₁ : V}
    (hisom : ∀ y ∈ H, ∀ v w, B (y v) (y w) = B v w) (hall : AutAll H U)
    (hn : 2 ≤ Module.finrank (ZMod 2) U) {a : U}
    (hfix : ∀ y ∈ transGroup H U hUH (a : V), y v₁ = v₁) : B v₁ a = 0 := by
  by_cases ha : a = 0
  · simp [ha]
  obtain ⟨s, hs⟩ := g10FourSplit_exists_notMem_span hn ha
  obtain ⟨f, hfa, hfs⟩ := g10Four_exists_dual U a s hs
  obtain ⟨k, hkY, hk⟩ := exists_mem_transGroup hUH hall f hfa
  have h2 := hisom k hkY.1 v₁ s
  rw [hfix k hkY, hk s, hfs, one_smul, map_add] at h2
  exact add_eq_left.1 h2

end Step1

variable [Finite V]

theorem g10FourSplit_exists_two_forms {U : Submodule (ZMod 2) V}
    (hn : 3 ≤ Module.finrank (ZMod 2) U) {a : U} (ha : a ≠ 0) :
    ∃ f₁ f₂ : U →ₗ[ZMod 2] ZMod 2, f₁ a = 0 ∧ f₂ a = 0 ∧ f₁ ≠ 0 ∧ f₂ ≠ 0 ∧ f₁ ≠ f₂ := by
  obtain ⟨s, hs⟩ := g10FourSplit_exists_notMem_span (U := U) (by omega) ha
  obtain ⟨f₁, hf₁a, hf₁s⟩ := g10Four_exists_dual U a s hs
  have hker := g10Four_finrank_ker_ge U f₁
  have hspan : Module.finrank (ZMod 2) (Submodule.span (ZMod 2) {a}) = 1 :=
    finrank_span_singleton ha
  obtain ⟨t, htk, ht⟩ : ∃ t ∈ LinearMap.ker f₁, t ∉ Submodule.span (ZMod 2) {a} := by
    by_contra hcon
    push Not at hcon
    have := Submodule.finrank_mono (show LinearMap.ker f₁ ≤ Submodule.span (ZMod 2) {a} from hcon)
    omega
  obtain ⟨f₂, hf₂a, hf₂t⟩ := g10Four_exists_dual U a t ht
  have htk' : f₁ t = 0 := htk
  refine ⟨f₁, f₂, hf₁a, hf₂a, ?_, ?_, ?_⟩
  · intro h
    rw [h] at hf₁s
    exact zero_ne_one hf₁s
  · intro h
    rw [h] at hf₂t
    exact zero_ne_one hf₂t
  · intro h
    rw [h] at htk'
    exact zero_ne_one (htk'.symm.trans hf₂t)

namespace G101Hyp

variable {B : LinearMap.BilinForm (ZMod 2) V} {Γ : Subgroup (V ≃ₗ[ZMod 2] V)} {v₁ : V}
  {W : Submodule (ZMod 2) V} {X X₀ : Subgroup (V ≃ₗ[ZMod 2] V)}
  (h : G101Hyp B Γ v₁ W X X₀)

include h

theorem split_sup_eq_top (Z : Submodule (ZMod 2) V) (hZ : Invariant X Z) (h1 : v₁ ∉ Z)
    (h2 : ∃ z ∈ Z, B v₁ z ≠ 0) : W ⊔ Z = ⊤ := by
  obtain ⟨hdim, -, -, -, -⟩ := h.counting Z hZ h1 h2
  have h3 := Submodule.finrank_sup_add_finrank_inf_eq W Z
  rw [h.inf_eq_bot Z hZ h1, finrank_bot] at h3
  exact Submodule.eq_top_of_finrank_eq (by omega)

theorem split_apply_sub_mem_span (Z : Submodule (ZMod 2) V) (hsup : W ⊔ Z = ⊤) {a : V}
    {x : V ≃ₗ[ZMod 2] V} (hx : x ∈ X) (hxZ : ∀ z ∈ Z, x z - z ∈ Submodule.span (ZMod 2) {a})
    (v : V) : x v - v ∈ Submodule.span (ZMod 2) {a, v₁} := by
  have hv : v ∈ W ⊔ Z := by rw [hsup]; trivial
  obtain ⟨w, hw, z, hz, rfl⟩ := Submodule.mem_sup.1 hv
  obtain ⟨f, -, hf⟩ := h.transvection x hx
  have hxw : x w = w + f ⟨w, hw⟩ • v₁ := hf ⟨w, hw⟩
  have e : x (w + z) - (w + z) = f ⟨w, hw⟩ • v₁ + (x z - z) := by
    rw [map_add, hxw]
    abel
  rw [e]
  exact Submodule.add_mem _ (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
    (Submodule.span_mono (by simp) (hxZ z hz))

theorem split_quadratic {H : Subgroup (V ≃ₗ[ZMod 2] V)} {U : Submodule (ZMod 2) V}
    (hUX : Invariant X U) (hUH : Invariant H U) (h1 : v₁ ∉ U) (h2 : ∃ u ∈ U, B v₁ u ≠ 0)
    (hXH : X ≤ H) (hfaith : FaithfulOn H U) (hall : AutAll H U) {a : U} (ha0 : a ≠ 0)
    (hαa : B v₁ a = 0) (hfix : ∀ y ∈ transGroup H U hUH (a : V), y v₁ = v₁) :
    ∀ y ∈ transGroup H U hUH (a : V), ∀ y' ∈ transGroup H U hUH (a : V), ∀ v : V,
      y' (y v - v) = y v - v := by
  obtain ⟨-, -, -, hfull, -⟩ := h.counting U hUX h1 h2
  obtain ⟨x, hxX, hx⟩ := hfull a hαa
  have hsup := h.split_sup_eq_top U hUX h1 h2
  have hxu : ∀ u ∈ U, x u - u ∈ Submodule.span (ZMod 2) {(a : V)} := fun u hu => by
    rw [hx ⟨u, hu⟩, add_sub_cancel_left]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)
  have hcomm := h.split_apply_sub_mem_span U hsup hxX hxu
  have hYfix : ∀ y' ∈ transGroup H U hUH (a : V), ∀ w ∈ Submodule.span (ZMod 2) {(a : V), v₁},
      y' w = w := by
    intro y' hy' w hw
    refine g10FourSplit_fix_span (fun s hs => ?_) hw
    rcases hs with rfl | hs
    · exact hy'.2.1
    · rw [Set.mem_singleton_iff.1 hs]
      exact hfix y' hy'
  intro y hy y' hy' v
  by_cases hf0 : ∀ u ∈ U, y u = u
  · have : y = 1 := g10FourSplit_eq_one_of_faithful hfaith hy.1 hf0
    simp [this]
  obtain ⟨f, hfa, hfy⟩ := exists_form_of_mem_transGroup ha0 hy.2.1 hy.2.2
  have hf : f ≠ 0 := by
    rintro rfl
    apply hf0
    intro u hu
    rw [hfy ⟨u, hu⟩]
    simp
  let α : U →ₗ[ZMod 2] ZMod 2 := (B v₁).domRestrict U
  have hα : α ≠ 0 := by
    obtain ⟨u, hu, hne⟩ := h2
    intro h0
    exact hne (by simpa [α] using LinearMap.congr_fun h0 ⟨u, hu⟩)
  obtain ⟨g, hga, hg⟩ := exists_linearEquiv_fix_dual U a ha0 α f hα hf hαa hfa
  obtain ⟨k, hkH, hk⟩ := hall g
  have hka : k (a : V) = a := by rw [hk a, hga]
  have hyk : y = k * x * k⁻¹ := by
    refine g10FourSplit_eq_of_faithful hfaith hy.1
      (H.mul_mem (H.mul_mem hkH (hXH hxX)) (H.inv_mem hkH)) fun u hu => ?_
    have hwU : (k⁻¹ : GLV V) u ∈ U := hUH k⁻¹ (H.inv_mem hkH) u hu
    let w : U := ⟨(k⁻¹ : GLV V) u, hwU⟩
    have hkw : k (w : V) = u := by simp [w]
    have hgw : g w = ⟨u, hu⟩ := Subtype.ext (by rw [← hk w]; exact hkw)
    have hfu : f ⟨u, hu⟩ = B v₁ (w : V) := by
      rw [← hgw]
      exact hg w
    rw [hfy ⟨u, hu⟩, hfu, LinearEquiv.mul_apply, LinearEquiv.mul_apply]
    show (u : V) + B v₁ (w : V) • (a : V) = k (x (w : V))
    rw [hx w, map_add, map_smul, hka, hkw]
  have hk'Y : k⁻¹ * y' * k ∈ transGroup H U hUH (a : V) := by
    have := conj_mem_transGroup hUH (H.inv_mem hkH) hy'
    have e : (k⁻¹ : GLV V) (a : V) = a := by
      calc (k⁻¹ : GLV V) (a : V) = k⁻¹ (k (a : V)) := by rw [hka]
        _ = a := by simp
    rwa [e, inv_inv] at this
  have e1 : y v - v = k (x (k⁻¹ v) - k⁻¹ v) := by rw [hyk]; simp
  have h5 := hYfix _ hk'Y _ (hcomm (k⁻¹ v))
  rw [e1]
  calc y' (k (x (k⁻¹ v) - k⁻¹ v)) = k ((k⁻¹ * y' * k) (x (k⁻¹ v) - k⁻¹ v)) := by simp
    _ = k (x (k⁻¹ v) - k⁻¹ v) := by rw [h5]

end G101Hyp

theorem exists_quadratic_four {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    {B : LinearMap.BilinForm (ZMod 2) V} {Γ : Subgroup (GLV V)} {v₁ : V}
    {W : Submodule (ZMod 2) V} {X X₀ : Subgroup (GLV V)} (hyp : G101Hyp B Γ v₁ W X X₀)
    (H : Subgroup (GLV V)) (hHΓ : H ≤ Γ) (hHn : ∀ γ ∈ Γ, ∀ h ∈ H, γ * h * γ⁻¹ ∈ H)
    (U : Submodule (ZMod 2) V) (hUX : Invariant X U) (hUH : Invariant H U) (h1 : v₁ ∉ U)
    (h2 : ∃ u ∈ U, B v₁ u ≠ 0) (hn3 : 3 ≤ Module.finrank (ZMod 2) U) (hiso : Isotropic B U)
    (hdim : 2 * Module.finrank (ZMod 2) U = Module.finrank (ZMod 2) V) (hXH : X ≤ H)
    (hfaith : FaithfulOn H U) (hall : AutAll H U) :
    ∃ E : Subgroup (GLV V), E ≤ H ∧ Nat.card E = 4 ∧
      (∃ a ∈ U, a ≠ 0 ∧ ∀ e ∈ E, ∀ u ∈ U, e u - u ∈ Submodule.span (ZMod 2) {a}) ∧
      (∀ e ∈ E, ∀ e' ∈ E, ∀ v : V, e (e' v - v) = e' v - v) := by
  have _ := hiso
  have _ := hdim
  obtain ⟨a₀, ha₀⟩ : ∃ a₀ : U, a₀ ≠ 0 :=
    (Module.finrank_pos_iff_exists_ne_zero (R := ZMod 2) (M := U)).1 (by omega)
  obtain ⟨k, hkH, hfix⟩ :=
    g10FourSplit_exists_conj_fix hUH hHΓ hHn hyp.odd_index hfaith (a₀ : V)
  let a₁ : U := g10FourRestrict H U hUH ⟨k⁻¹, H.inv_mem hkH⟩ a₀
  have ha₁V : (a₁ : V) = k⁻¹ (a₀ : V) := rfl
  have ha₁ : a₁ ≠ 0 := fun h0 =>
    ha₀ ((LinearEquiv.map_eq_zero_iff (g10FourRestrict H U hUH ⟨k⁻¹, H.inv_mem hkH⟩)).1 h0)
  have hfix' : ∀ y ∈ transGroup H U hUH (a₁ : V), y v₁ = v₁ := by
    rw [ha₁V]
    exact hfix
  have hperp : B v₁ a₁ = 0 :=
    g10FourSplit_perp_of_fix hUH (fun y hy v w => hyp.isometry y (hHΓ hy) v w) hall (by omega)
      hfix'
  have hq := hyp.split_quadratic hUX hUH h1 h2 hXH hfaith hall ha₁ hperp hfix'
  set Y := transGroup H U hUH (a₁ : V)
  obtain ⟨n, hn⟩ : ∃ n : ℕ, Nat.card ↥Y = 2 ^ n :=
    (transGroup_isPGroup hUH hfaith (a₁ : V)).exists_card_eq
  obtain ⟨f₁, f₂, hf₁a, hf₂a, hf₁, hf₂, hf12⟩ := g10FourSplit_exists_two_forms hn3 ha₁
  obtain ⟨y₁, hy₁Y, hy₁⟩ := exists_mem_transGroup hUH hall f₁ hf₁a
  obtain ⟨y₂, hy₂Y, hy₂⟩ := exists_mem_transGroup hUH hall f₂ hf₂a
  have hne1 : ∀ {f : U →ₗ[ZMod 2] ZMod 2} {y : GLV V}, f ≠ 0 →
      (∀ u : U, y (u : V) = (u : V) + f u • (a₁ : V)) → y ≠ 1 := by
    intro f y hf hy hy1
    obtain ⟨u, hu⟩ : ∃ u, f u ≠ 0 := by
      by_contra hcon
      push Not at hcon
      exact hf (LinearMap.ext hcon)
    have h3 := hy u
    rw [hy1] at h3
    have h4 : f u • (a₁ : V) = 0 := add_eq_left.1 h3.symm
    rcases smul_eq_zero.1 h4 with h0 | h0
    · exact hu h0
    · exact ha₁ (Subtype.ext h0)
  have hne2 : y₁ ≠ y₂ := by
    intro h12
    obtain ⟨u, hu⟩ : ∃ u, f₁ u ≠ f₂ u := by
      by_contra hcon
      push Not at hcon
      exact hf12 (LinearMap.ext hcon)
    have h3 := hy₁ u
    rw [h12, hy₂ u] at h3
    have h4 : f₂ u • (a₁ : V) = f₁ u • (a₁ : V) := add_left_cancel h3
    have h0 : (a₁ : V) ≠ 0 := fun h0 => ha₁ (Subtype.ext h0)
    exact hu (smul_left_injective (ZMod 2) h0 h4).symm
  have hcard : 2 < Nat.card ↥Y := by
    have := Fintype.ofFinite ↥Y
    rw [Nat.card_eq_fintype_card]
    refine Fintype.two_lt_card_iff.2 ⟨1, ⟨y₁, hy₁Y⟩, ⟨y₂, hy₂Y⟩, ?_, ?_, ?_⟩
    · exact fun h0 => hne1 hf₁ hy₁ (congrArg Subtype.val h0).symm
    · exact fun h0 => hne1 hf₂ hy₂ (congrArg Subtype.val h0).symm
    · exact fun h0 => hne2 (congrArg Subtype.val h0)
  have hn2 : 2 ≤ n := by
    by_contra hlt
    push Not at hlt
    have : 2 ^ n ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  obtain ⟨K, hK⟩ := Sylow.exists_subgroup_card_pow_prime (G := ↥Y) 2 (n := 2)
    (by rw [hn]; exact pow_dvd_pow 2 hn2)
  refine ⟨K.map Y.subtype, ?_, ?_, ⟨(a₁ : V), a₁.2, fun h0 => ha₁ (Subtype.ext h0), ?_⟩, ?_⟩
  · rintro _ ⟨y, -, rfl⟩
    exact y.2.1
  · rw [Subgroup.card_map_of_injective Y.subtype_injective, hK]
    norm_num
  · rintro e ⟨y, -, rfl⟩ u hu
    exact y.2.2.2 u hu
  · rintro e ⟨y, -, rfl⟩ e' ⟨y', -, rfl⟩ v
    exact hq y' y'.2 y y.2 v

end CFSG.Quasithin
