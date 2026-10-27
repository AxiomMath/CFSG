module

public import CFSG.Quasithin.EmptyFaithful.T1531O4Syl
public import CFSG.Quasithin.EmptyFaithful.T1531Gold2

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.S1417 CFSG.Quasithin.T1531O4

section Bridge

variable {G : Type} [Group G] {V : Subgroup G} (hV : IsElemAbelian 2 V)

@[expose] def modOf (E : Subgroup G) : Subgroup (IntMod V hV) := E.comap (inclMod hV)

theorem mem_modOf {E : Subgroup G} {w : IntMod V hV} : w ∈ modOf hV E ↔ w.val ∈ E := Iff.rfl

theorem map_modOf {E : Subgroup G} (hEV : E ≤ V) : (modOf hV E).map (inclMod hV) = E := by
  ext x
  constructor
  · rintro ⟨w, hw, rfl⟩
    exact hw
  · intro hx
    exact ⟨IntMod.mk hV ⟨x, hEV hx⟩, hx, rfl⟩

theorem card_modOf {E : Subgroup G} (hEV : E ≤ V) : Nat.card (modOf hV E) = Nat.card E := by
  have := Subgroup.card_map_of_injective (inclMod_injective hV) (K := modOf hV E)
  rw [map_modOf hV hEV] at this
  exact this.symm

theorem mem_normalizer_iff_stab {E : Subgroup G} (hEV : E ≤ V) {x : G}
    (hx : x ∈ Subgroup.normalizer (V : Set G)) :
    x ∈ Subgroup.normalizer (E : Set G) ↔ convI hV ⟨x, hx⟩ ∈ stabSub (modOf hV E) := by
  have := mem_normalizer_map_inclMod_iff hV hx (modOf hV E)
  rwa [map_modOf hV hEV] at this

theorem autI_inf_normalizer {K E : Subgroup G} (hEV : E ≤ V) :
    autI hV (K ⊓ Subgroup.normalizer (E : Set G)) = autI hV K ⊓ stabSub (modOf hV E) := by
  ext φ
  constructor
  · intro hφ
    obtain ⟨g, ⟨hgK, hgn⟩, rfl⟩ := (mem_autI hV).1 hφ
    exact ⟨convI_mem_autI hV hgK g.2, (mem_normalizer_iff_stab hV hEV g.2).1 hgn⟩
  · rintro ⟨hφK, hφS⟩
    obtain ⟨g, hgK, rfl⟩ := (mem_autI hV).1 hφK
    have hgn : (g : G) ∈ Subgroup.normalizer (E : Set G) :=
      (mem_normalizer_iff_stab hV hEV g.2).2 hφS
    exact convI_mem_autI hV (Subgroup.mem_inf.2 ⟨hgK, hgn⟩) g.2

theorem isLine_modOf {L₁ L₂ : Subgroup (MulAut (IntMod V hV))} {E : Subgroup G} (hEV : E ≤ V)
    (hcard : Nat.card E = 4) (h₁ : E ⊓ (commV L₁).map (inclMod hV) = ⊥)
    (h₂ : E ⊓ (commV L₂).map (inclMod hV) = ⊥) : IsLine (commV L₁) (commV L₂) (modOf hV E) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [card_modOf hV hEV]
    exact hcard
  · rw [eq_bot_iff]
    rintro w ⟨hwE, hw₁⟩
    have : w.val ∈ E ⊓ (commV L₁).map (inclMod hV) := ⟨hwE, ⟨w, hw₁, rfl⟩⟩
    rw [h₁, Subgroup.mem_bot] at this
    exact Subgroup.mem_bot.mpr (IntMod.val_injective this)
  · rw [eq_bot_iff]
    rintro w ⟨hwE, hw₂⟩
    have : w.val ∈ E ⊓ (commV L₂).map (inclMod hV) := ⟨hwE, ⟨w, hw₂, rfl⟩⟩
    rw [h₂, Subgroup.mem_bot] at this
    exact Subgroup.mem_bot.mpr (IntMod.val_injective this)

end Bridge

section LineFacts

variable {G : Type} [Group G] [Finite G] {T Mc M V₁ V₂ E : Subgroup G} {t : G}

theorem line_facts (c : Ctx153 G T Mc M V₁ V₂ t) (L : LineData153 T M V₁ V₂ E) :
    Nat.card (autOn (TE153 T E) (VZ T M)) = 4 ∧
    (∀ g ∈ autOn (TE153 T E) (VZ T M), g * g = 1) ∧
    (∀ g ∈ autOn (TE153 T E) (VZ T M), ∀ h ∈ autOn (TE153 T E) (VZ T M), g * h = h * g) ∧
    autOn (TE153 T E) (VZ T M) ≠ autOn (Sgp153 T V₁) (VZ T M) ∧
    (∀ (hV : IsElemAbelian 2 (VZ T M)) (g : MulAut ↥(VZ T M)),
      g ∈ autOn (TE153 T E) (VZ T M) ↔ g ∈ autOn T (VZ T M) ∧ IsDicksonEven153 hV g) ∧
    Nat.card (autOn T (VZ T M)) = 8 ∧
    quasithinOmegaOneCenter T ≤ E ∧
    (∃ t₀ ∈ TE153 T E, ∃ e ∈ E, t₀ * e * t₀⁻¹ ≠ e) ∧
    (∀ x ∈ M, x ^ 3 = 1 → x ∈ Subgroup.centralizer (E : Set G) →
      x ∈ Subgroup.centralizer (VZ T M : Set G)) := by
  obtain ⟨hV, L₁, L₂, tb, hS, rfl, rfl, -⟩ := c.decomp.model
  have hMN : M ≤ Subgroup.normalizer (VZ T M : Set G) := c.hyp.le_normalizer
  have hTM : T ≤ M := c.hyp.T_le
  have hEV : E ≤ VZ T M := L.le_V
  have hexp : ∀ w : IntMod (VZ T M) hV, w ^ 2 = 1 := fun w => IntMod.sq_eq_one w
  have hÊ : IsLine (commV L₁) (commV L₂) (modOf hV E) :=
    isLine_modOf hV hEV L.card_eq L.totSingular.2.1 L.totSingular.2.2
  have hT' : IsSylowTwoOf (autI hV T) (autI hV M) :=
    B2F.isSylowTwoOf_autI hV hMN c.hyp.isSylowTwoOf
  have hTE' : IsSylowTwoOf (autI hV T ⊓ stabSub (modOf hV E))
      (autI hV M ⊓ stabSub (modOf hV E)) := by
    have h1 := B2F.isSylowTwoOf_autI hV (H := M ⊓ Subgroup.normalizer (E : Set G))
      (T := T ⊓ Subgroup.normalizer (E : Set G)) (inf_le_left.trans hMN) L.sylow
    rwa [autI_inf_normalizer hV hEV, autI_inf_normalizer hV hEV] at h1
  obtain ⟨s₁, s₂, τ, a₁, a₂, hF⟩ := hS.exists_sylowFacts hT'
  obtain ⟨c1, c2, c3, c4, c5, c6, c7⟩ := sylow_line hS hexp hT' hÊ hTE' hF
  have hTEeq : autOn (TE153 T E) (VZ T M) = autI hV T ⊓ stabSub (modOf hV E) :=
    autI_inf_normalizer hV hEV
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hTEeq]; exact c1
  · rw [hTEeq]; exact c2
  · rw [hTEeq]; exact c3
  · intro h
    apply c4
    rw [← hTEeq, h]
    exact autI_nS hV hS hTM
  · intro hV' g
    rw [hTEeq]
    constructor
    · rintro ⟨hg1, hg2⟩
      exact ⟨hg1, (c5 g hg1).1 hg2⟩
    · rintro ⟨hg1, hg2⟩
      exact ⟨hg1, (c5 g hg1).2 hg2⟩
  · exact hS.card_T hT'
  · intro z hz
    have hzV : z ∈ VZ T M := c.hyp.Z_le_VZ hz
    have hw := c6 (IntMod.mk hV ⟨z, hzV⟩) (fun x hx => by
      obtain ⟨g, hgT, rfl⟩ := (mem_autI hV).1 hx
      apply IntMod.val_injective
      rw [convI_apply_val]
      have hc := Subgroup.mem_centralizer_iff.mp (c.hyp.T_le_centralizer_Z hgT) z hz
      show (g : G) * z * (g : G)⁻¹ = z
      rw [← hc]
      group)
    exact hw
  · obtain ⟨g, hg, ê, hê, hne⟩ := c7
    have hg' : g ∈ autI hV (TE153 T E) := by
      have h0 := hg
      rw [← hTEeq] at h0
      exact h0
    obtain ⟨t₀, ht₀, rfl⟩ := (mem_autI hV).1 hg'
    refine ⟨t₀, ht₀, ê.val, hê, fun h => hne (IntMod.val_injective ?_)⟩
    rw [convI_apply_val]
    exact h
  · intro x hxM hx3 hxE
    have hxN : x ∈ Subgroup.normalizer (VZ T M : Set G) := hMN hxM
    have hxX : convI hV ⟨x, hxN⟩ ∈ autI hV M := convI_mem_autI hV hxM hxN
    have h3 : (convI hV ⟨x, hxN⟩) ^ 3 = 1 := by
      rw [← map_pow]
      have : (⟨x, hxN⟩ : ↥(Subgroup.normalizer (VZ T M : Set G))) ^ 3 = 1 := Subtype.ext hx3
      rw [this, map_one]
    have hfix : ∀ e ∈ modOf hV E, convI hV ⟨x, hxN⟩ e = e := fun e he => by
      apply IntMod.val_injective
      rw [convI_apply_val]
      have := Subgroup.mem_centralizer_iff.mp hxE e.val he
      rw [← this]
      group
    have h1 := eq_one_of_cube_of_fix hS hÊ hxX h3 hfix
    exact (convI_eq_one_iff hV ⟨x, hxN⟩).1 h1

theorem Y_facts (h113 : StageLemma14113) (c : Ctx153 G T Mc M V₁ V₂ t)
    (L : LineData153 T M V₁ V₂ E) :
    ⁅VZ T M, YE153 Mc M E⁆ = VZ T M ∧
    ∃ y ∈ YE153 Mc M E, (∃ e ∈ E, y * e * y⁻¹ ≠ e) ∧
      y ^ 3 ∈ Subgroup.centralizer (VZ T M : Set G) := by
  obtain ⟨hV, L₁, L₂, tb, hS, rfl, rfl, -⟩ := c.decomp.model
  have hMN : M ≤ Subgroup.normalizer (VZ T M : Set G) := c.hyp.le_normalizer
  have hEV : E ≤ VZ T M := L.le_V
  have hexp : ∀ w : IntMod (VZ T M) hV, w ^ 2 = 1 := fun w => IntMod.sq_eq_one w
  have hÊ : IsLine (commV L₁) (commV L₂) (modOf hV E) :=
    isLine_modOf hV hEV L.card_eq L.totSingular.2.1 L.totSingular.2.2
  obtain ⟨p, hpL, hp3, hpS, ⟨ê, hê, hpê⟩, hpfix⟩ := exists_cube_stab hS hÊ
  have hpX : p ∈ autI hV M := hS.le_X_sup hpL
  have hpY : p ∈ autI hV (Y153 Mc M) := by
    have h1 : autI hV (Y153 Mc M) = oTwoUpper (autI hV M) := c.hyp.autOn_Y153 h113
    rw [h1]
    exact mem_oTwoUpper_of_odd hpX (odd_orderOf_of_pow_three hp3)
  obtain ⟨y₀, hy₀Y, hy₀p⟩ := (mem_autI hV).1 hpY
  have hy₀E : (y₀ : G) ∈ Subgroup.normalizer (E : Set G) :=
    (mem_normalizer_iff_stab hV hEV y₀.2).2 (hy₀p ▸ hpS)
  obtain ⟨k, hk⟩ := exists_pow_mem_oTwoUpper (Y153 Mc M ⊓ Subgroup.normalizer (E : Set G))
    (x := (y₀ : G)) ⟨hy₀Y, hy₀E⟩
  have hYEN : YE153 Mc M E ≤ Subgroup.normalizer (VZ T M : Set G) :=
    ((oTwoUpper_le _).trans (inf_le_left.trans (Y153_le Mc M))).trans hMN
  have hyYE : ((y₀ : G) ^ 2 ^ k) ^ 2 ^ k ∈ YE153 Mc M E := (YE153 Mc M E).pow_mem hk _
  have hyN : ((y₀ : G) ^ 2 ^ k) ^ 2 ^ k ∈ Subgroup.normalizer (VZ T M : Set G) := hYEN hyYE
  have hconv : convI hV ⟨((y₀ : G) ^ 2 ^ k) ^ 2 ^ k, hyN⟩ = p := by
    have e1 : (⟨((y₀ : G) ^ 2 ^ k) ^ 2 ^ k, hyN⟩ : ↥(Subgroup.normalizer (VZ T M : Set G))) =
        y₀ ^ (2 ^ k * 2 ^ k) := Subtype.ext (by simp [pow_mul])
    have h4 : (2 ^ k * 2 ^ k) % 3 = 1 := by
      rw [← mul_pow]
      norm_num [Nat.pow_mod]
    rw [e1, map_pow, hy₀p, pow_eq_pow_mod (2 ^ k * 2 ^ k) hp3, h4, pow_one]
  refine ⟨?_, ((y₀ : G) ^ 2 ^ k) ^ 2 ^ k, hyYE, ⟨ê.val, hê, fun h => hpê ?_⟩, ?_⟩
  · rw [commutator_eq_map_commV hV hYEN]
    have hpYE : p ∈ autI hV (YE153 Mc M E) := hconv ▸ convI_mem_autI hV hyYE hyN
    have hfix : fixV (Subgroup.zpowers p) = ⊥ := by
      refine (Subgroup.eq_bot_iff_forall _).2 fun w hw => hpfix w ?_
      exact mem_fixV_zpowers_iff.mp hw
    have hrk := rk_commV_add_rk_fixV p
    rw [hfix, rk_bot] at hrk
    have htop : commV (Subgroup.zpowers p) = ⊤ :=
      eq_of_le_of_rk_le hexp le_top (by rw [rk_top]; omega)
    have hle : commV (Subgroup.zpowers p) ≤ commV (autI hV (YE153 Mc M E)) :=
      Subgroup.closure_mono fun w ⟨x, hx, v, hxv⟩ =>
        ⟨x, (Subgroup.zpowers_le.2 hpYE) hx, v, hxv⟩
    rw [htop] at hle
    rw [eq_top_iff.2 hle, map_inclMod_top]
  · apply IntMod.val_injective
    show (p ê).val = ê.val
    rw [← hconv, convI_apply_val]
    exact h
  · have h3 : convI hV ⟨(((y₀ : G) ^ 2 ^ k) ^ 2 ^ k) ^ 3, (Subgroup.normalizer _).pow_mem hyN 3⟩ = 1 := by
      have e1 : (⟨(((y₀ : G) ^ 2 ^ k) ^ 2 ^ k) ^ 3, (Subgroup.normalizer _).pow_mem hyN 3⟩ :
          ↥(Subgroup.normalizer (VZ T M : Set G))) =
          (⟨((y₀ : G) ^ 2 ^ k) ^ 2 ^ k, hyN⟩ : ↥(Subgroup.normalizer (VZ T M : Set G))) ^ 3 :=
        Subtype.ext rfl
      rw [e1, map_pow, hconv, hp3]
    exact (convI_eq_one_iff hV _).1 h3

end LineFacts

end CFSG.Quasithin
