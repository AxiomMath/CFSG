module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtH23Six5Defs
public import CFSG.Quasithin.EmptyFaithful.S151Basic

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

section Conj

variable {V : Subgroup G} {hV : IsElemAbelian 2 V}

omit [Finite G] in
theorem conj_val {m : G} (hm : m ∈ Subgroup.normalizer (V : Set G)) (w : IntMod V hV) :
    m * IntMod.val w * m⁻¹ = IntMod.val (convI hV ⟨m, hm⟩ w) :=
  (convI_apply_val hV ⟨m, hm⟩ w).symm

omit [Finite G] in
theorem mem_normalizer_map {U : Subgroup (IntMod V hV)} {m : G}
    (hm : m ∈ Subgroup.normalizer (V : Set G)) (hs : ∀ w, w ∈ U ↔ convI hV ⟨m, hm⟩ w ∈ U) :
    m ∈ Subgroup.normalizer ((U.map (valHomI hV) : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro h
  constructor
  · intro hh
    obtain ⟨w, hw, rfl⟩ := (Subgroup.mem_map.1 hh)
    show m * IntMod.val w * m⁻¹ ∈ U.map (valHomI hV)
    rw [conj_val hm w]
    exact Subgroup.mem_map.2 ⟨_, (hs w).1 hw, rfl⟩
  · intro hh
    obtain ⟨u, hu, hue⟩ := Subgroup.mem_map.1 hh
    have hhV : h ∈ V := (Subgroup.mem_normalizer_iff.mp hm h).2 (by
      rw [← hue]
      exact IntMod.val_mem u)
    have hw' : (convI hV ⟨m, hm⟩ (IntMod.mk hV ⟨h, hhV⟩)) = u := by
      apply IntMod.val_injective
      rw [← conj_val hm]
      exact hue.symm
    refine Subgroup.mem_map.2 ⟨IntMod.mk hV ⟨h, hhV⟩, (hs _).2 (hw' ▸ hu), rfl⟩

omit [Finite G] in
theorem stab_of_mem_normalizer_map {U : Subgroup (IntMod V hV)} {m : G}
    (hm : m ∈ Subgroup.normalizer (V : Set G))
    (hn : m ∈ Subgroup.normalizer ((U.map (valHomI hV) : Subgroup G) : Set G)) :
    ∀ w, w ∈ U ↔ convI hV ⟨m, hm⟩ w ∈ U := by
  intro w
  have hval : ∀ u : IntMod V hV, u ∈ U ↔ IntMod.val u ∈ (U.map (valHomI hV) : Subgroup G) := by
    intro u
    constructor
    · intro hu
      exact Subgroup.mem_map.2 ⟨u, hu, rfl⟩
    · intro hu
      obtain ⟨u', hu', hue⟩ := Subgroup.mem_map.1 hu
      have : u' = u := IntMod.val_injective hue
      exact this ▸ hu'
  rw [hval, hval, ← conj_val hm w]
  exact Subgroup.mem_normalizer_iff.mp hn (IntMod.val w)

omit [Finite G] in
theorem isPGroup_autI_of {P : Subgroup G} (hP : IsPGroup 2 P) : IsPGroup 2 (autI hV P) := by
  rintro ⟨φ, hφ⟩
  obtain ⟨⟨g, hgN⟩, hg, rfl⟩ := (mem_autI hV).1 hφ
  obtain ⟨k, hk⟩ := hP ⟨g, hg⟩
  refine ⟨k, Subtype.ext ?_⟩
  have h1 : (⟨g, hgN⟩ : Subgroup.normalizer (V : Set G)) ^ 2 ^ k = 1 :=
    Subtype.ext (by simpa using congrArg Subtype.val hk)
  show (convI hV ⟨g, hgN⟩) ^ 2 ^ k = 1
  rw [← map_pow, h1, map_one]

end Conj

namespace Six5Data

variable {T M V : Subgroup G} {hV : IsElemAbelian 2 V} (d : Six5Data T M V hV)
include d

theorem hTN : T ≤ Subgroup.normalizer (V : Set G) := d.hTM.trans d.hMN

theorem hnorm : ∀ g ∈ autI hV M, ∀ z ∈ d.S.A₁ ⊔ d.S.A₂, g * z * g⁻¹ ∈ d.S.A₁ ⊔ d.S.A₂ := by
  rw [d.hsup]
  intro g hg z hz
  exact mem_Jhat_conj hg hz

theorem mem_V₁_iff {x : G} : x ∈ d.V₁ ↔ ∃ w ∈ d.S.W₁, IntMod.val w = x := by
  unfold V₁
  rw [Subgroup.mem_map]
  rfl

theorem mem_V₂_iff {x : G} : x ∈ d.V₂ ↔ ∃ w ∈ d.S.W₂, IntMod.val w = x := by
  unfold V₂
  rw [Subgroup.mem_map]
  rfl

theorem val_mem_V₁ {w : IntMod V hV} (hw : w ∈ d.S.W₁) : IntMod.val w ∈ d.V₁ :=
  (d.mem_V₁_iff).2 ⟨w, hw, rfl⟩

theorem val_mem_V₂ {w : IntMod V hV} (hw : w ∈ d.S.W₂) : IntMod.val w ∈ d.V₂ :=
  (d.mem_V₂_iff).2 ⟨w, hw, rfl⟩

theorem V₁_le_V : d.V₁ ≤ V := by
  intro x hx
  obtain ⟨w, -, rfl⟩ := (d.mem_V₁_iff).1 hx
  exact IntMod.val_mem w

theorem V₂_le_V : d.V₂ ≤ V := by
  intro x hx
  obtain ⟨w, -, rfl⟩ := (d.mem_V₂_iff).1 hx
  exact IntMod.val_mem w

theorem V₁_inf_V₂ : d.V₁ ⊓ d.V₂ = ⊥ := by
  unfold V₁ V₂
  rw [← Subgroup.map_inf _ _ _ (IntMod.val_injective (hV := hV))]
  have : d.S.W₁ ⊓ d.S.W₂ = ⊥ := d.S.winf
  rw [this, Subgroup.map_bot]

theorem V₁_sup_V₂ : d.V₁ ⊔ d.V₂ = V := by
  unfold V₁ V₂
  rw [← Subgroup.map_sup]
  have : d.S.W₁ ⊔ d.S.W₂ = ⊤ := d.S.wsup
  rw [this, ← MonoidHom.range_eq_map]
  ext x
  constructor
  · rintro ⟨w, rfl⟩
    exact IntMod.val_mem w
  · intro hx
    exact ⟨IntMod.mk hV ⟨x, hx⟩, rfl⟩

theorem card_V₁ : Nat.card d.V₁ = 16 := by
  unfold V₁
  rw [Subgroup.card_map_of_injective (IntMod.val_injective (hV := hV))]
  exact d.S.card_W₁ d.hcard

theorem card_V₂ : Nat.card d.V₂ = 16 := by
  unfold V₂
  rw [Subgroup.card_map_of_injective (IntMod.val_injective (hV := hV))]
  exact d.S.card_W₂ d.hcard

theorem not_mem_normalizer_of_swap {m : G} (hm : ∀ v ∈ d.V₁, m * v * m⁻¹ ∈ d.V₂) :
    m ∉ Subgroup.normalizer (d.V₁ : Set G) := by
  intro hN
  obtain ⟨v, hv, hv1⟩ : ∃ v ∈ d.V₁, v ≠ 1 := by
    by_contra hcon
    push Not at hcon
    have hb : d.V₁ = ⊥ := (Subgroup.eq_bot_iff_forall _).2 hcon
    have h16 := d.card_V₁
    rw [hb, Subgroup.card_bot] at h16
    omega
  have h1 : m * v * m⁻¹ ∈ d.V₁ := (Subgroup.mem_normalizer_iff.mp hN v).1 hv
  have h2 : m * v * m⁻¹ ∈ d.V₁ ⊓ d.V₂ := ⟨h1, hm v hv⟩
  rw [d.V₁_inf_V₂, Subgroup.mem_bot] at h2
  apply hv1
  calc v = m⁻¹ * (m * v * m⁻¹) * m := by group
    _ = 1 := by rw [h2]; group

end Six5Data

end CFSG.Quasithin
