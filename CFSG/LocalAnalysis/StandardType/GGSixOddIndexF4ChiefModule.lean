module

public import Mathlib.GroupTheory.QuotientGroup.Defs
public import Mathlib.GroupTheory.Subgroup.Centralizer
public import Mathlib.GroupTheory.Coset.Card
public import Mathlib.Tactic.Group

public section

namespace CFSG.StandardType

namespace F4Chief

variable {R G : Type} [Group R] [Group G]

@[expose] noncomputable def sectionConj (χ : R →* G) {V : Subgroup G}
    (hV : χ.range ≤ Subgroup.normalizer (V : Set G)) : R →* MulAut V :=
  V.normalizerMonoidHom.comp (χ.codRestrict _ fun r => hV ⟨r, rfl⟩)

theorem coe_sectionConj (χ : R →* G) {V : Subgroup G}
    (hV : χ.range ≤ Subgroup.normalizer (V : Set G)) (r : R) (v : V) :
    ((sectionConj χ hV r v : V) : G) = χ r * v * (χ r)⁻¹ :=
  rfl

theorem sectionConj_map_subgroupOf (χ : R →* G) {N V : Subgroup G}
    (hV : χ.range ≤ Subgroup.normalizer (V : Set G))
    (hN : χ.range ≤ Subgroup.normalizer (N : Set G)) (r : R) :
    (N.subgroupOf V).map (sectionConj χ hV r : V →* V) = N.subgroupOf V := by
  have key : ∀ r : R, (N.subgroupOf V).map (sectionConj χ hV r : V →* V) ≤ N.subgroupOf V := by
    intro r
    rintro _ ⟨v, hv, rfl⟩
    have hv' : (v : G) ∈ N := Subgroup.mem_subgroupOf.mp hv
    rw [Subgroup.mem_subgroupOf]
    change ((sectionConj χ hV r v : V) : G) ∈ N
    rw [coe_sectionConj]
    exact (Subgroup.mem_normalizer_iff.mp (hN ⟨r, rfl⟩) v).mp hv'
  refine le_antisymm (key r) ?_
  intro v hv
  refine ⟨sectionConj χ hV r⁻¹ v, key r⁻¹ ⟨v, hv, rfl⟩, ?_⟩
  change sectionConj χ hV r (sectionConj χ hV r⁻¹ v) = v
  rw [← MulAut.mul_apply, ← map_mul, mul_inv_cancel, map_one, MulAut.one_apply]

@[expose] noncomputable def sectionAct (χ : R →* G) {N V : Subgroup G}
    (hV : χ.range ≤ Subgroup.normalizer (V : Set G))
    (hN : χ.range ≤ Subgroup.normalizer (N : Set G)) [(N.subgroupOf V).Normal] :
    R →* MulAut (V ⧸ N.subgroupOf V) where
  toFun r := QuotientGroup.congr (N.subgroupOf V) (N.subgroupOf V) (sectionConj χ hV r)
    (sectionConj_map_subgroupOf χ hV hN r)
  map_one' := by
    ext x
    induction x using QuotientGroup.induction_on with
    | H v => simp
  map_mul' r₁ r₂ := by
    ext x
    induction x using QuotientGroup.induction_on with
    | H v => simp [MulAut.mul_apply]

theorem sectionAct_mk (χ : R →* G) {N V : Subgroup G}
    (hV : χ.range ≤ Subgroup.normalizer (V : Set G))
    (hN : χ.range ≤ Subgroup.normalizer (N : Set G)) [(N.subgroupOf V).Normal] (r : R) (v : V) :
    sectionAct χ hV hN r (v : V ⧸ N.subgroupOf V) = ((sectionConj χ hV r v : V) :
      V ⧸ N.subgroupOf V) :=
  rfl

theorem exists_fixed_of_module [Finite G] (χ : R →* G) {N V : Subgroup G} (hNV : N < V)
    (hVN : V ≤ Subgroup.normalizer (N : Set G))
    (hYN : χ.range ≤ Subgroup.normalizer (N : Set G))
    (hYV : χ.range ≤ Subgroup.normalizer (V : Set G)) (hsq : ∀ x ∈ V, x ^ 2 ∈ N)
    (hirr : ∀ W : Subgroup G, N ≤ W → W ≤ V → χ.range ≤ Subgroup.normalizer (W : Set G) →
      W = N ∨ W = V) (e : R)
    (hmod : ∀ (Q : Type) [Group Q] [Finite Q], (∀ x : Q, x ^ 2 = 1) → Nontrivial Q →
      ∀ ρ : R →* MulAut Q, (∀ W : Subgroup Q, (∀ r, ∀ x ∈ W, ρ r x ∈ W) → W = ⊥ ∨ W = ⊤) →
        ∃ x : Q, x ≠ 1 ∧ ρ e x = x) :
    ∃ v ∈ V, v ∉ N ∧ χ e * v * (χ e)⁻¹ * v⁻¹ ∈ N := by
  have hNVle : N ≤ V := hNV.le
  have : (N.subgroupOf V).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hNVle).mpr hVN
  have hmk1 : ∀ v : V, ((v : V ⧸ N.subgroupOf V) = 1 ↔ (v : G) ∈ N) := fun v => by
    rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
  have hQ2 : ∀ x : V ⧸ N.subgroupOf V, x ^ 2 = 1 := by
    intro x
    induction x using QuotientGroup.induction_on with
    | H v =>
      rw [← QuotientGroup.mk_pow, hmk1]
      exact hsq v v.2
  obtain ⟨v₀, hv₀V, hv₀N⟩ := IsConcreteLE.exists_of_lt hNV
  have hQnt : Nontrivial (V ⧸ N.subgroupOf V) :=
    ⟨⟨((⟨v₀, hv₀V⟩ : V) : V ⧸ N.subgroupOf V), 1, fun h => hv₀N ((hmk1 _).mp h)⟩⟩
  have hρirr : ∀ W : Subgroup (V ⧸ N.subgroupOf V),
      (∀ r, ∀ x ∈ W, sectionAct χ hYV hYN r x ∈ W) → W = ⊥ ∨ W = ⊤ := by
    intro W hW
    set W' : Subgroup G := (W.comap (QuotientGroup.mk' (N.subgroupOf V))).map V.subtype
    have hmemW' : ∀ v : V, (v : G) ∈ W' ↔ (v : V ⧸ N.subgroupOf V) ∈ W := by
      intro v
      constructor
      · rintro ⟨v', hv', hvv'⟩
        have : v' = v := Subtype.ext hvv'
        rw [← this]
        exact hv'
      · intro h
        exact ⟨v, h, rfl⟩
    have hNW' : N ≤ W' := by
      intro n hn
      have h := (hmemW' ⟨n, hNVle hn⟩).mpr (by rw [(hmk1 _).mpr hn]; exact W.one_mem)
      exact h
    have hW'V : W' ≤ V := Subgroup.map_subtype_le _
    have hconj : ∀ (r : R) (v : V), (v : V ⧸ N.subgroupOf V) ∈ W →
        χ r * (v : G) * (χ r)⁻¹ ∈ W' := by
      intro r v hv
      rw [← coe_sectionConj χ hYV r v, hmemW', ← sectionAct_mk χ hYV hYN]
      exact hW r _ hv
    have hYW' : χ.range ≤ Subgroup.normalizer (W' : Set G) := by
      rintro _ ⟨r, rfl⟩
      rw [Subgroup.mem_normalizer_iff]
      intro x
      constructor
      · rintro ⟨v, hv, rfl⟩
        exact hconj r v hv
      · rintro ⟨v', hv', hv'eq⟩
        have hx : x = χ r⁻¹ * (v' : G) * (χ r⁻¹)⁻¹ := by
          change (v' : G) = _ at hv'eq
          rw [hv'eq, map_inv, inv_inv]
          group
        rw [hx]
        exact hconj r⁻¹ v' hv'
    rcases hirr W' hNW' hW'V hYW' with h | h
    · left
      rw [eq_bot_iff]
      intro x hx
      obtain ⟨v, rfl⟩ := QuotientGroup.mk_surjective x
      rw [Subgroup.mem_bot]
      exact (hmk1 v).mpr (by rw [← h]; exact (hmemW' v).mpr hx)
    · right
      rw [eq_top_iff]
      intro x _
      obtain ⟨v, rfl⟩ := QuotientGroup.mk_surjective x
      exact (hmemW' v).mp (by rw [h]; exact v.2)
  obtain ⟨x, hx1, hxe⟩ := hmod (V ⧸ N.subgroupOf V) hQ2 hQnt (sectionAct χ hYV hYN) hρirr
  obtain ⟨v, rfl⟩ := QuotientGroup.mk_surjective x
  refine ⟨v, v.2, fun hvN => hx1 ((hmk1 v).mpr hvN), ?_⟩
  change sectionAct χ hYV hYN e (v : V ⧸ N.subgroupOf V) = v at hxe
  rw [sectionAct_mk, QuotientGroup.eq, Subgroup.mem_subgroupOf] at hxe
  have hc : (χ e * (v : G) * (χ e)⁻¹)⁻¹ * v ∈ N := by
    rw [← coe_sectionConj χ hYV e v]
    simpa using hxe
  have hc' := (Subgroup.mem_normalizer_iff.mp (hVN v.2) _).mp (N.inv_mem hc)
  have heq : (v : G) * ((χ e * (v : G) * (χ e)⁻¹)⁻¹ * v)⁻¹ * (v : G)⁻¹ =
      χ e * v * (χ e)⁻¹ * (v : G)⁻¹ := by group
  rwa [heq] at hc'

end F4Chief

end CFSG.StandardType
