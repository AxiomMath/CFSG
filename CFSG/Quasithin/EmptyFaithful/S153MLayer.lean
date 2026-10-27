module

public import CFSG.Quasithin.EmptyFaithful.S153MMod
public import CFSG.Quasithin.EmptyFaithful.S1565H

public section

namespace CFSG.Quasithin

open CFSG.Open hiding StatedSL StatedSp
open CFSG.QuasithinUnique CFSG.Quasithin.S1565
open scoped Pointwise commutatorElement

namespace S153M

section Layer

attribute [local instance] commGroupOfFact

variable {G : Type} [Group G] {V₁ W U H K₀ : Subgroup G}

theorem modMk_mem_subM_commutator_iff (hUV : U ≤ Subgroup.normalizer (V₁ : Set G))
    (hK₀U : ⁅U, K₀⁆ ≤ U) {u : G} (hu : u ∈ U) :
    modMk hUV u hu ∈ subM V₁ U ⁅U, K₀⁆ ↔ u ∈ ⁅U, K₀⁆ ⊔ V₁ := by
  have hsup : subM V₁ U ⁅U, K₀⁆ = subM V₁ U (⁅U, K₀⁆ ⊔ V₁) := by
    unfold subM
    rw [tildeOf_sup_self (hK₀U.trans hUV)]
  rw [hsup]
  exact modMk_mem_subM_iff hUV (le_sup_right : V₁ ≤ ⁅U, K₀⁆ ⊔ V₁) hu

variable [Fact (IsElemAbelian 2 (tildeOf V₁ U))]

theorem modMk_mem_fixModSub_iff (hV₁H : H ≤ Subgroup.normalizer (V₁ : Set G))
    (hUH : H ≤ Subgroup.normalizer (U : Set G)) (hUV : U ≤ Subgroup.normalizer (V₁ : Set G))
    (hK₀H : K₀ ≤ H) (hV₁W : V₁ ≤ W) {u : G} (hu : u ∈ U) :
    modMk hUV u hu ∈ fixModSub (actH hV₁H hUH) (K₀.subgroupOf H) (subM V₁ U W) ↔
      ∀ k ∈ K₀, k * u * k⁻¹ * u⁻¹ ∈ W := by
  have hku : ∀ k ∈ K₀, k * u * k⁻¹ ∈ U := fun k hk =>
    (Subgroup.mem_normalizer_iff.mp (hUH (hK₀H hk)) u).mp hu
  have key : ∀ (k : G) (hk : k ∈ K₀), actH hV₁H hUH ⟨k, hK₀H hk⟩ (modMk hUV u hu) *
      (modMk hUV u hu)⁻¹ = modMk hUV (k * u * k⁻¹ * u⁻¹) (U.mul_mem (hku k hk) (U.inv_mem hu)) := by
    intro k hk
    rw [actH_modMk hV₁H hUV hUH ⟨k, hK₀H hk⟩ hu, ← modMk_inv hUV hu,
      ← modMk_mul hUV (hku k hk) (U.inv_mem hu)]
  constructor
  · intro h k hk
    have h1 := h ⟨k, hK₀H hk⟩ (Subgroup.mem_subgroupOf.mpr hk)
    rw [key k hk, modMk_mem_subM_iff hUV hV₁W _] at h1
    exact h1
  · intro h s hs
    have hs' : (s : G) ∈ K₀ := Subgroup.mem_subgroupOf.mp hs
    have h1 := key (s : G) hs'
    have e : s = ⟨(s : G), hK₀H hs'⟩ := rfl
    rw [e, h1, modMk_mem_subM_iff hUV hV₁W _]
    exact h _ hs'

section E

variable [Fact (IsElemAbelian 2 (tildeOf W U))]

theorem modMk_mem_fixV_iff (hWH : H ≤ Subgroup.normalizer (W : Set G))
    (hUH : H ≤ Subgroup.normalizer (U : Set G)) (hUW : U ≤ Subgroup.normalizer (W : Set G))
    (hK₀H : K₀ ≤ H) {u : G} (hu : u ∈ U) :
    modMk hUW u hu ∈ fixV ((K₀.subgroupOf H).map (actH hWH hUH)) ↔
      ∀ k ∈ K₀, k * u * k⁻¹ * u⁻¹ ∈ W := by
  have hku : ∀ k ∈ K₀, k * u * k⁻¹ ∈ U := fun k hk =>
    (Subgroup.mem_normalizer_iff.mp (hUH (hK₀H hk)) u).mp hu
  constructor
  · intro h k hk
    have h1 := h (actH hWH hUH ⟨k, hK₀H hk⟩)
      ⟨⟨k, hK₀H hk⟩, Subgroup.mem_subgroupOf.mpr hk, rfl⟩
    rw [actH_modMk hWH hUW hUH ⟨k, hK₀H hk⟩ hu] at h1
    exact (modMk_conj_eq_iff hUW hu (hku k hk)).mp h1
  · intro h x hx
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
    have hy' : (y : G) ∈ K₀ := Subgroup.mem_subgroupOf.mp hy
    rw [actH_modMk hWH hUW hUH y hu]
    exact (modMk_conj_eq_iff hUW hu (hku _ hy')).mpr (h _ hy')

omit [Fact (IsElemAbelian 2 (tildeOf V₁ U))] in
theorem modMk_mem_commV (hV₁W : V₁ ≤ W) (hWU : W ≤ U) (hWH : H ≤ Subgroup.normalizer (W : Set G))
    (hUH : H ≤ Subgroup.normalizer (U : Set G)) (hUW : U ≤ Subgroup.normalizer (W : Set G))
    (hUV : U ≤ Subgroup.normalizer (V₁ : Set G)) (hK₀H : K₀ ≤ H) (hK₀U : ⁅U, K₀⁆ ≤ U)
    {u : G} (hu : u ∈ U) (hmem : u ∈ ⁅U, K₀⁆ ⊔ V₁) :
    modMk hUW u hu ∈ commV ((K₀.subgroupOf H).map (actH hWH hUH)) := by
  set L : Subgroup (MulAut ↥(tildeOf W U)) := (K₀.subgroupOf H).map (actH hWH hUH) with hL
  have hmul := Subgroup.coe_mul_of_left_le_normalizer_right ⁅U, K₀⁆ V₁ (hK₀U.trans hUV)
  have hu' : u ∈ ((⁅U, K₀⁆ : Subgroup G) : Set G) * (V₁ : Set G) := by
    rw [← hmul]; exact hmem
  obtain ⟨c, hc, v, hv, rfl⟩ := hu'
  have hcU : c ∈ U := hK₀U hc
  have key : ∀ c' : G, c' ∈ ⁅U, K₀⁆ → ∃ hc'U : c' ∈ U, modMk hUW c' hc'U ∈ commV L := by
    intro c' hc'
    rw [Subgroup.commutator_def] at hc'
    refine Subgroup.closure_induction (p := fun c' _ => ∃ hc'U : c' ∈ U, modMk hUW c' hc'U ∈ commV L)
      ?_ ?_ ?_ ?_ hc'
    · rintro _ ⟨p, hp, q, hq, rfl⟩
      have hpU : p ∈ U := hp
      have hqH : q ∈ H := hK₀H hq
      have hqp : q * p * q⁻¹ ∈ U := (Subgroup.mem_normalizer_iff.mp (hUH hqH) p).mp hpU
      have hc'U : ⁅p, q⁆ ∈ U := by
        rw [commutatorElement_def]
        have : p * q * p⁻¹ * q⁻¹ = p * (q * p⁻¹ * q⁻¹) := by group
        rw [this]
        refine U.mul_mem hpU ?_
        have := U.inv_mem hqp
        simpa [mul_assoc] using this
      refine ⟨hc'U, ?_⟩
      have h1 : modMk hUW (⁅p, q⁆) hc'U = (actH hWH hUH ⟨q, hqH⟩ (modMk hUW p hpU) *
          (modMk hUW p hpU)⁻¹)⁻¹ := by
        rw [actH_modMk hWH hUW hUH ⟨q, hqH⟩ hpU, ← modMk_inv hUW hpU,
          ← modMk_mul hUW hqp (U.inv_mem hpU), ← modMk_inv hUW (U.mul_mem hqp (U.inv_mem hpU))]
        congr 1
        rw [commutatorElement_def]
        group
      rw [h1]
      refine Subgroup.inv_mem _ (Subgroup.subset_closure ⟨actH hWH hUH ⟨q, hqH⟩, ?_, modMk hUW p hpU, rfl⟩)
      exact ⟨⟨q, hqH⟩, Subgroup.mem_subgroupOf.mpr hq, rfl⟩
    · exact ⟨U.one_mem, by rw [modMk_one]; exact Subgroup.one_mem _⟩
    · rintro x y - - ⟨hxU, hx⟩ ⟨hyU, hy⟩
      refine ⟨U.mul_mem hxU hyU, ?_⟩
      rw [modMk_mul hUW hxU hyU]
      exact Subgroup.mul_mem _ hx hy
    · rintro x - ⟨hxU, hx⟩
      refine ⟨U.inv_mem hxU, ?_⟩
      rw [modMk_inv hUW hxU]
      exact Subgroup.inv_mem _ hx
  obtain ⟨hcU', hc⟩ := key c hc
  have hvW : v ∈ W := hV₁W hv
  have hvU : v ∈ U := hWU hvW
  have hcv : modMk hUW (c * v) hu = modMk hUW c hcU' * modMk hUW v hvU :=
    modMk_mul hUW hcU' hvU
  rw [hcv, (modMk_eq_one_iff hUW hvU).mpr hvW, mul_one]
  exact hc

theorem layer_transfer
    (hV₁W : V₁ ≤ W) (hWU : W ≤ U) (hV₁H : H ≤ Subgroup.normalizer (V₁ : Set G))
    (hWH : H ≤ Subgroup.normalizer (W : Set G)) (hUH : H ≤ Subgroup.normalizer (U : Set G))
    (hUV : U ≤ Subgroup.normalizer (V₁ : Set G)) (hUW : U ≤ Subgroup.normalizer (W : Set G))
    (hK₀H : K₀ ≤ H) (hK₀U : ⁅U, K₀⁆ ≤ U) (t₀ : ↥H)
    (hb : ∀ e ∈ commV ((K₀.subgroupOf H).map (actH hWH hUH)),
      actH hWH hUH t₀ e * e⁻¹ ∈ fixV ((K₀.subgroupOf H).map (actH hWH hUH)) ⊓
          commV ((K₀.subgroupOf H).map (actH hWH hUH)) →
        e ∈ fixV ((K₀.subgroupOf H).map (actH hWH hUH)) ⊓
          commV ((K₀.subgroupOf H).map (actH hWH hUH))) :
    ∀ a ∈ subM V₁ U ⁅U, K₀⁆,
      actH hV₁H hUH t₀ a * a⁻¹ ∈ subM V₁ U ⁅U, K₀⁆ ⊓
          fixModSub (actH hV₁H hUH) (K₀.subgroupOf H) (subM V₁ U W) →
        a ∈ subM V₁ U ⁅U, K₀⁆ ⊓ fixModSub (actH hV₁H hUH) (K₀.subgroupOf H) (subM V₁ U W) := by
  intro a haUk hhyp
  obtain ⟨a', haU, hau⟩ := exists_mk_of_mem_tilde a
  have ha : a = modMk hUV (a' : G) haU := Subtype.ext hau.symm
  set u : G := (a' : G) with hu_def
  set x : G := (t₀ : G) with hx_def
  have hxu : x * u * x⁻¹ ∈ U := (Subgroup.mem_normalizer_iff.mp (hUH t₀.2) u).mp haU
  have hc : x * u * x⁻¹ * u⁻¹ ∈ U := U.mul_mem hxu (U.inv_mem haU)
  have hkey1 : actH hV₁H hUH t₀ (modMk hUV u haU) * (modMk hUV u haU)⁻¹ =
      modMk hUV (x * u * x⁻¹ * u⁻¹) hc := by
    rw [actH_modMk hV₁H hUV hUH t₀ haU, ← modMk_inv hUV haU, ← modMk_mul hUV hxu (U.inv_mem haU)]
  have hkey2 : actH hWH hUH t₀ (modMk hUW u haU) * (modMk hUW u haU)⁻¹ =
      modMk hUW (x * u * x⁻¹ * u⁻¹) hc := by
    rw [actH_modMk hWH hUW hUH t₀ haU, ← modMk_inv hUW haU, ← modMk_mul hUW hxu (U.inv_mem haU)]
  subst ha
  rw [hkey1] at hhyp
  obtain ⟨hc1, hc2⟩ := Subgroup.mem_inf.mp hhyp
  have hmemc := (modMk_mem_subM_commutator_iff hUV hK₀U hc).mp hc1
  have hfixc := (modMk_mem_fixModSub_iff hV₁H hUH hUV hK₀H hV₁W hc).mp hc2
  have hmemu := (modMk_mem_subM_commutator_iff hUV hK₀U haU).mp haUk
  have hu_comm := modMk_mem_commV hV₁W hWU hWH hUH hUW hUV hK₀H hK₀U haU hmemu
  have hc_comm := modMk_mem_commV hV₁W hWU hWH hUH hUW hUV hK₀H hK₀U hc hmemc
  have hc_fix := (modMk_mem_fixV_iff hWH hUH hUW hK₀H hc).mpr hfixc
  obtain ⟨hu_fix, -⟩ := Subgroup.mem_inf.mp
    (hb _ hu_comm (by rw [hkey2]; exact Subgroup.mem_inf.mpr ⟨hc_fix, hc_comm⟩))
  have hfixu := (modMk_mem_fixV_iff hWH hUH hUW hK₀H haU).mp hu_fix
  exact Subgroup.mem_inf.mpr ⟨haUk, (modMk_mem_fixModSub_iff hV₁H hUH hUV hK₀H hV₁W haU).mpr hfixu⟩

end E

end Layer

end S153M

end CFSG.Quasithin
