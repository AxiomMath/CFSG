module

public import CFSG.SignalizerFunctorTheorem.McBride.Prelim.DirectProduct

public section

namespace CFSG.SignalizerFunctorTheorem.McBride.Nonsolv

variable {G : Type*} [Group G] {K L W : Subgroup G}

theorem exists_mul_of_isDirectPair (h : IsDirectPair K L W) {w : G} (hw : w ∈ W) :
    ∃ k ∈ K, ∃ l ∈ L, k * l = w :=
  (mem_sup_iff_of_commute h.commute).mp (h.sup_eq ▸ hw)

theorem eq_of_mul_eq_of_isDirectPair (h : IsDirectPair K L W) {k k' l l' : G} (hk : k ∈ K)
    (hk' : k' ∈ K) (hl : l ∈ L) (hl' : l' ∈ L) (hkl : k * l = k' * l') : k = k' ∧ l = l' := by
  have h1 : k'⁻¹ * k = l' * l⁻¹ := by
    calc k'⁻¹ * k = k'⁻¹ * (k * l) * l⁻¹ := by group
      _ = l' * l⁻¹ := by rw [hkl]; group
  have hmem : k'⁻¹ * k ∈ K ⊓ L :=
    Subgroup.mem_inf.mpr ⟨mul_mem (inv_mem hk') hk, h1 ▸ mul_mem hl' (inv_mem hl)⟩
  rw [h.inf_eq_bot, Subgroup.mem_bot, inv_mul_eq_one] at hmem
  subst hmem
  exact ⟨rfl, mul_left_cancel hkl⟩

private noncomputable def pairProjFun (h : IsDirectPair K L W) (w : ↥W) : ↥K :=
  ⟨(exists_mul_of_isDirectPair h w.2).choose, (exists_mul_of_isDirectPair h w.2).choose_spec.1⟩

private theorem pairProjFun_eq (h : IsDirectPair K L W) {k l : G} (hk : k ∈ K) (hl : l ∈ L)
    (w : ↥W) (hw : k * l = w) : ((pairProjFun h w : K) : G) = k := by
  obtain ⟨hk₀, l₀, hl₀, hw₀⟩ := (exists_mul_of_isDirectPair h w.2).choose_spec
  exact (eq_of_mul_eq_of_isDirectPair h hk₀ hk hl₀ hl (hw₀.trans hw.symm)).1

noncomputable def pairProj (h : IsDirectPair K L W) : ↥W →* ↥K where
  toFun := pairProjFun h
  map_one' := by
    apply Subtype.ext
    exact pairProjFun_eq h (one_mem K) (one_mem L) 1 (by simp)
  map_mul' a b := by
    obtain ⟨k₁, hk₁, l₁, hl₁, h₁⟩ := exists_mul_of_isDirectPair h a.2
    obtain ⟨k₂, hk₂, l₂, hl₂, h₂⟩ := exists_mul_of_isDirectPair h b.2
    apply Subtype.ext
    rw [Subgroup.coe_mul, pairProjFun_eq h hk₁ hl₁ a h₁, pairProjFun_eq h hk₂ hl₂ b h₂]
    refine pairProjFun_eq h (mul_mem hk₁ hk₂) (mul_mem hl₁ hl₂) (a * b) ?_
    have hc := (h.commute k₂ hk₂ l₁ hl₁).eq
    calc k₁ * k₂ * (l₁ * l₂) = k₁ * (k₂ * l₁) * l₂ := by group
      _ = k₁ * (l₁ * k₂) * l₂ := by rw [hc]
      _ = (k₁ * l₁) * (k₂ * l₂) := by group
      _ = ((a * b : ↥W) : G) := by rw [h₁, h₂]; rfl

theorem pairProj_mul (h : IsDirectPair K L W) {k : G} (hk : k ∈ K) {l : G} (hl : l ∈ L)
    (hkl : k * l ∈ W) : ((pairProj h ⟨k * l, hkl⟩ : K) : G) = k :=
  pairProjFun_eq h hk hl _ rfl

theorem pairProj_spec (h : IsDirectPair K L W) (w : W) :
    ∃ l ∈ L, ((pairProj h w : K) : G) * l = w := by
  obtain ⟨l, hl, hw⟩ := (exists_mul_of_isDirectPair h w.2).choose_spec.2
  exact ⟨l, hl, hw⟩

theorem pairProj_of_mem_left (h : IsDirectPair K L W) {k : G} (hk : k ∈ K) (hkW : k ∈ W) :
    ((pairProj h ⟨k, hkW⟩ : K) : G) = k := by
  have := pairProj_mul h hk (one_mem L) (by simpa using hkW)
  simpa using this

theorem pairProj_of_mem_right (h : IsDirectPair K L W) {l : G} (hl : l ∈ L) (hlW : l ∈ W) :
    pairProj h ⟨l, hlW⟩ = 1 := by
  apply Subtype.ext
  have := pairProj_mul h (one_mem K) hl (by simpa using hlW)
  simpa using this

theorem proj_eq_map_pairProj (h : IsDirectPair K L W) {X : Subgroup G} (hXW : X ≤ W) :
    proj K L X = ((X.subgroupOf W).map (pairProj h)).map K.subtype := by
  ext x
  rw [mem_proj_iff h.commute]
  constructor
  · rintro ⟨hxK, l, hl, hxl⟩
    refine ⟨pairProj h ⟨x * l, hXW hxl⟩, ⟨⟨x * l, hXW hxl⟩, hxl, rfl⟩, ?_⟩
    exact pairProj_mul h hxK hl _
  · rintro ⟨y, ⟨w, hw, rfl⟩, rfl⟩
    obtain ⟨l, hl, hwl⟩ := pairProj_spec h w
    exact ⟨(pairProj h w).2, l, hl, hwl ▸ hw⟩

theorem isSolvable_proj (h : IsDirectPair K L W) {X : Subgroup G} (hXW : X ≤ W)
    (hX : Group.IsSolvable X) : Group.IsSolvable (proj K L X) := by
  rw [proj_eq_map_pairProj h hXW]
  have h1 : Group.IsSolvable (X.subgroupOf W) :=
    Group.isSolvable_of_isSolvable_injective
      (f := (Subgroup.subgroupOfEquivOfLe hXW).toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe hXW).injective
  have h2 : Group.IsSolvable ((X.subgroupOf W).map (pairProj h)) :=
    Group.isSolvable_of_surjective (MonoidHom.subgroupMap_surjective (pairProj h) _)
  exact Group.isSolvable_of_isSolvable_injective
    (f := (Subgroup.equivMapOfInjective _ K.subtype K.subtype_injective).symm.toMonoidHom)
    (MulEquiv.injective _)

theorem conj_mem_proj (h : IsDirectPair K L W) {X : Subgroup G} {k l : G} (hk : k ∈ K)
    (hl : l ∈ L) (hc : k * l ∈ Subgroup.normalizer (X : Set G)) {x : G}
    (hx : x ∈ proj K L X) : k * x * k⁻¹ ∈ proj K L X := by
  rw [mem_proj_iff h.commute] at hx ⊢
  obtain ⟨hxK, m, hm, hxm⟩ := hx
  have hlm : l * m * l⁻¹ ∈ L := mul_mem (mul_mem hl hm) (inv_mem hl)
  refine ⟨mul_mem (mul_mem hk hxK) (inv_mem hk), l * m * l⁻¹, hlm, ?_⟩
  have h1 := (Subgroup.mem_normalizer_iff.mp hc (x * m)).mp hxm
  have hxl : x * l = l * x := (h.commute x hxK l hl).eq
  have hky : k⁻¹ * (l * m * l⁻¹) = (l * m * l⁻¹) * k⁻¹ :=
    ((h.commute k hk _ hlm).inv_left).eq
  have e : k * l * (x * m) * (k * l)⁻¹ = k * x * k⁻¹ * (l * m * l⁻¹) := by
    calc k * l * (x * m) * (k * l)⁻¹ = k * (l * x) * m * l⁻¹ * k⁻¹ := by group
      _ = k * (x * l) * m * l⁻¹ * k⁻¹ := by rw [hxl]
      _ = k * x * ((l * m * l⁻¹) * k⁻¹) := by group
      _ = k * x * (k⁻¹ * (l * m * l⁻¹)) := by rw [hky]
      _ = k * x * k⁻¹ * (l * m * l⁻¹) := by group
  rwa [e] at h1

theorem mem_normalizer_proj (h : IsDirectPair K L W) {X : Subgroup G} {k l : G} (hk : k ∈ K)
    (hl : l ∈ L) (hc : k * l ∈ Subgroup.normalizer (X : Set G)) :
    k ∈ Subgroup.normalizer (proj K L X : Set G) := by
  have hc' : k⁻¹ * l⁻¹ ∈ Subgroup.normalizer (X : Set G) := by
    have : k⁻¹ * l⁻¹ = (k * l)⁻¹ := by
      rw [mul_inv_rev]
      exact (h.commute k hk l hl).inv_inv.eq
    rw [this]
    exact inv_mem hc
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨fun hx => conj_mem_proj h hk hl hc hx, fun hx => ?_⟩
  have := conj_mem_proj h (inv_mem hk) (inv_mem hl) hc' hx
  rwa [show k⁻¹ * (k * x * k⁻¹) * k⁻¹⁻¹ = x by group] at this

theorem pairProj_mem_normalizer_proj (h : IsDirectPair K L W) {X : Subgroup G} {c : ↥W}
    (hc : (c : G) ∈ Subgroup.normalizer (X : Set G)) :
    ((pairProj h c : K) : G) ∈ Subgroup.normalizer (proj K L X : Set G) := by
  obtain ⟨l, hl, hcl⟩ := pairProj_spec h c
  exact mem_normalizer_proj h (pairProj h c).2 hl (hcl ▸ hc)

theorem mem_normalizer_proj_of_normalizes (hcomm : ∀ x ∈ K, ∀ y ∈ L, Commute x y)
    {X : Subgroup G} {g : G} (hK : g ∈ Subgroup.normalizer (K : Set G))
    (hL : g ∈ Subgroup.normalizer (L : Set G)) (hX : g ∈ Subgroup.normalizer (X : Set G)) :
    g ∈ Subgroup.normalizer (proj K L X : Set G) := by
  have key : ∀ g : G, g ∈ Subgroup.normalizer (K : Set G) →
      g ∈ Subgroup.normalizer (L : Set G) → g ∈ Subgroup.normalizer (X : Set G) →
      ∀ x ∈ proj K L X, g * x * g⁻¹ ∈ proj K L X := by
    intro g hK hL hX x hx
    rw [mem_proj_iff hcomm] at hx ⊢
    obtain ⟨hxK, m, hm, hxm⟩ := hx
    refine ⟨(Subgroup.mem_normalizer_iff.mp hK x).mp hxK, g * m * g⁻¹,
      (Subgroup.mem_normalizer_iff.mp hL m).mp hm, ?_⟩
    have := (Subgroup.mem_normalizer_iff.mp hX (x * m)).mp hxm
    rwa [show g * (x * m) * g⁻¹ = g * x * g⁻¹ * (g * m * g⁻¹) by group] at this
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨key g hK hL hX x, fun hx => ?_⟩
  have := key g⁻¹ (inv_mem hK) (inv_mem hL) (inv_mem hX) _ hx
  rwa [show g⁻¹ * (g * x * g⁻¹) * g⁻¹⁻¹ = x by group] at this

end CFSG.SignalizerFunctorTheorem.McBride.Nonsolv
