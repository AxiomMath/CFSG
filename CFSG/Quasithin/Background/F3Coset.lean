module

public import CFSG.Quasithin.Background.F3Cover
public import CFSG.Quasithin.Background.F7Geometry

public section

namespace CFSG.Quasithin

open CFSG.Quasithin.F7

universe u v

namespace CosetGeom

variable {G : Type u} [Group G] {G₀ G₁ G₂ : Subgroup G}

instance : GraphAction ↥G₀ (graph G₀ G₁ G₂) := ⟨fun g _ _ => smul_adj g⟩

section Cover

variable {H : Type v} [Group H] {H₀ H₁ H₂ : Subgroup H}

@[expose] def cosetMap {X Y : Type*} [Group X] [Group Y] (A : Subgroup X) (B : Subgroup Y) (f : X →* Y)
    (h : A ≤ B.comap f) : X ⧸ A → Y ⧸ B :=
  Quotient.map' f (fun a b hab => by
    rw [QuotientGroup.leftRel_apply] at hab ⊢
    simpa using h hab)

@[simp] theorem cosetMap_mk {X Y : Type*} [Group X] [Group Y] (A : Subgroup X) (B : Subgroup Y)
    (f : X →* Y) (h : A ≤ B.comap f) (a : X) :
    cosetMap A B f h (a : X ⧸ A) = (f a : Y ⧸ B) := rfl

theorem cosetMap_smul {X Y : Type*} [Group X] [Group Y] (A : Subgroup X) (B : Subgroup Y)
    (f : X →* Y) (h : A ≤ B.comap f) (g : X) (c : X ⧸ A) :
    cosetMap A B f h (g • c) = f g • cosetMap A B f h c := by
  induction c using QuotientGroup.induction_on with
  | H a => simp [cosetMap_mk, smul_eq_mul]

@[expose] def restrictHom (θ : G →* H) (G₀ : Subgroup G) (H₀ : Subgroup H) (h0 : ∀ x ∈ G₀, θ x ∈ H₀) :
    ↥G₀ →* ↥H₀ where
  toFun x := ⟨θ (x : G), h0 x x.2⟩
  map_one' := Subtype.ext (map_one θ)
  map_mul' x y := Subtype.ext (map_mul θ (x : G) (y : G))

@[simp] theorem coe_restrictHom (θ : G →* H) (G₀ : Subgroup G) (H₀ : Subgroup H)
    (h0 : ∀ x ∈ G₀, θ x ∈ H₀) (x : ↥G₀) : (restrictHom θ G₀ H₀ h0 x : H) = θ (x : G) := rfl

@[expose] def cover (θ : G →* H) (h0 : ∀ x ∈ G₀, θ x ∈ H₀) (h1 : ∀ x ∈ G₁, θ x ∈ H₁)
    (h2 : ∀ x ∈ G₂, θ x ∈ H₂) : CosetGeom G₀ G₁ G₂ → CosetGeom H₀ H₁ H₂ :=
  Sum.map (cosetMap (G₁.subgroupOf G₀) (H₁.subgroupOf H₀) (restrictHom θ G₀ H₀ h0)
      (fun x hx => h1 x hx))
    (cosetMap (G₂.subgroupOf G₀) (H₂.subgroupOf H₀) (restrictHom θ G₀ H₀ h0)
      (fun x hx => h2 x hx))

theorem adj_γ₀_inr_iff {y : ↥G₀ ⧸ G₂.subgroupOf G₀} :
    (graph G₀ G₁ G₂).Adj (γ₀ G₀ G₁ G₂) (Sum.inr y) ↔
      ∃ g : ↥G₀, (g : G) ∈ G₁ ∧ (g : ↥G₀ ⧸ G₂.subgroupOf G₀) = y := by
  rw [γ₀, adj_inl_inr]
  constructor
  · rintro ⟨g, h1, h2⟩
    refine ⟨g, ?_, h2⟩
    have := QuotientGroup.eq.mp h1
    rw [Subgroup.mem_subgroupOf] at this
    simpa using G₁.inv_mem this
  · rintro ⟨g, h1, h2⟩
    refine ⟨g, ?_, h2⟩
    rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
    simpa using G₁.inv_mem h1

theorem adj_γ₁_inl_iff {x : ↥G₀ ⧸ G₁.subgroupOf G₀} :
    (graph G₀ G₁ G₂).Adj (γ₁ G₀ G₁ G₂) (Sum.inl x) ↔
      ∃ g : ↥G₀, (g : G) ∈ G₂ ∧ (g : ↥G₀ ⧸ G₁.subgroupOf G₀) = x := by
  rw [γ₁, adj_inr_inl]
  constructor
  · rintro ⟨g, h1, h2⟩
    refine ⟨g, ?_, h1⟩
    have := QuotientGroup.eq.mp h2
    rw [Subgroup.mem_subgroupOf] at this
    simpa using G₂.inv_mem this
  · rintro ⟨g, h1, h2⟩
    refine ⟨g, h2, ?_⟩
    rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
    simpa using G₂.inv_mem h1

end Cover

structure CoverData {H : Type v} [Group H] (θ : G →* H) (G₁ G₂ : Subgroup G) (H₁ H₂ : Subgroup H) :
    Prop where
  inj₁ : ∀ x ∈ G₁, θ x = 1 → x = 1
  inj₂ : ∀ x ∈ G₂, θ x = 1 → x = 1
  map₁ : G₁.map θ = H₁
  map₂ : G₂.map θ = H₂
  inter : (G₁ ⊓ G₂).map θ = H₁ ⊓ H₂

namespace CoverData

variable {H : Type v} [Group H] {θ : G →* H} {H₁ H₂ : Subgroup H} (hd : CoverData θ G₁ G₂ H₁ H₂)

include hd in
theorem le₀ : ∀ x ∈ G₁ ⊔ G₂, θ x ∈ H₁ ⊔ H₂ := by
  intro x hx
  have h : G₁ ⊔ G₂ ≤ (H₁ ⊔ H₂).comap θ := by
    rw [← Subgroup.map_le_iff_le_comap, Subgroup.map_sup, hd.map₁, hd.map₂]
  exact h hx

include hd in
theorem le₁ : ∀ x ∈ G₁, θ x ∈ H₁ := fun _ hx => hd.map₁ ▸ Subgroup.mem_map_of_mem θ hx

include hd in
theorem le₂ : ∀ x ∈ G₂, θ x ∈ H₂ := fun _ hx => hd.map₂ ▸ Subgroup.mem_map_of_mem θ hx

@[expose] def hom0 : ↥(G₁ ⊔ G₂) →* ↥(H₁ ⊔ H₂) := restrictHom θ (G₁ ⊔ G₂) (H₁ ⊔ H₂) hd.le₀

@[simp] theorem coe_hom0 (g : ↥(G₁ ⊔ G₂)) : (hd.hom0 g : H) = θ g := rfl

theorem hom0_surjective : Function.Surjective hd.hom0 := by
  rintro ⟨h, hh⟩
  have : h ∈ (G₁ ⊔ G₂).map θ := by
    rw [Subgroup.map_sup, hd.map₁, hd.map₂]; exact hh
  obtain ⟨g, hg, rfl⟩ := this
  exact ⟨⟨g, hg⟩, rfl⟩

@[expose] def Θ : CosetGeom (G₁ ⊔ G₂) G₁ G₂ → CosetGeom (H₁ ⊔ H₂) H₁ H₂ :=
  cover θ hd.le₀ hd.le₁ hd.le₂

theorem Θ_smul (g : ↥(G₁ ⊔ G₂)) (v : CosetGeom (G₁ ⊔ G₂) G₁ G₂) : hd.Θ (g • v) = hd.hom0 g • hd.Θ v := by
  cases v with
  | inl x =>
    rw [smul_inl]
    show Sum.inl _ = Sum.inl _
    exact congrArg Sum.inl (cosetMap_smul _ _ _ _ g x)
  | inr y =>
    rw [smul_inr]
    show Sum.inr _ = Sum.inr _
    exact congrArg Sum.inr (cosetMap_smul _ _ _ _ g y)

theorem Θ_γ₀ : hd.Θ (γ₀ (G₁ ⊔ G₂) G₁ G₂) = γ₀ (H₁ ⊔ H₂) H₁ H₂ := by
  show Sum.inl _ = Sum.inl _
  refine congrArg Sum.inl ?_
  exact (cosetMap_mk _ _ _ _ 1).trans (congrArg _ (map_one hd.hom0))

theorem Θ_γ₁ : hd.Θ (γ₁ (G₁ ⊔ G₂) G₁ G₂) = γ₁ (H₁ ⊔ H₂) H₁ H₂ := by
  show Sum.inr _ = Sum.inr _
  refine congrArg Sum.inr ?_
  exact (cosetMap_mk _ _ _ _ 1).trans (congrArg _ (map_one hd.hom0))

theorem Θ_inl (g : ↥(G₁ ⊔ G₂)) :
    hd.Θ (Sum.inl (g : ↥(G₁ ⊔ G₂) ⧸ G₁.subgroupOf (G₁ ⊔ G₂))) =
      Sum.inl ((hd.hom0 g : ↥(H₁ ⊔ H₂)) : ↥(H₁ ⊔ H₂) ⧸ H₁.subgroupOf (H₁ ⊔ H₂)) := rfl

theorem Θ_inr (g : ↥(G₁ ⊔ G₂)) :
    hd.Θ (Sum.inr (g : ↥(G₁ ⊔ G₂) ⧸ G₂.subgroupOf (G₁ ⊔ G₂))) =
      Sum.inr ((hd.hom0 g : ↥(H₁ ⊔ H₂)) : ↥(H₁ ⊔ H₂) ⧸ H₂.subgroupOf (H₁ ⊔ H₂)) := rfl

theorem mem_of_map_mem {A B : Subgroup G} {A' B' : Subgroup H}
    (hA : ∀ x ∈ A, θ x = 1 → x = 1) (hAB : (A ⊓ B).map θ = A' ⊓ B')
    (hA' : ∀ x ∈ A, θ x ∈ A') {g₁ g₂ : G} (h₁ : g₁ ∈ A) (h₂ : g₂ ∈ A)
    (h : θ (g₁⁻¹ * g₂) ∈ B') : g₁⁻¹ * g₂ ∈ B := by
  have hg : g₁⁻¹ * g₂ ∈ A := A.mul_mem (A.inv_mem h₁) h₂
  have hmem : θ (g₁⁻¹ * g₂) ∈ A' ⊓ B' := ⟨hA' _ hg, h⟩
  rw [← hAB] at hmem
  obtain ⟨k, hk, hkθ⟩ := hmem
  have h3 : k⁻¹ * (g₁⁻¹ * g₂) ∈ A := A.mul_mem (A.inv_mem hk.1) hg
  have h4 : θ (k⁻¹ * (g₁⁻¹ * g₂)) = 1 := by rw [map_mul, map_inv, hkθ]; simp
  have h5 := hA _ h3 h4
  have : g₁⁻¹ * g₂ = k := by
    have h6 := congrArg (fun x => k * x) h5
    simpa using h6
  rw [this]
  exact hk.2

theorem isLocIso_γ₀ :
    IsLocIso (graph (G₁ ⊔ G₂) G₁ G₂) (graph (H₁ ⊔ H₂) H₁ H₂) hd.Θ (γ₀ (G₁ ⊔ G₂) G₁ G₂) where
  inj a b ha hb hab := by
    cases a with
    | inl x => exact (not_adj_inl_inl ha).elim
    | inr y₁ =>
      cases b with
      | inl x => exact (not_adj_inl_inl hb).elim
      | inr y₂ =>
        obtain ⟨g₁, hg₁, rfl⟩ := adj_γ₀_inr_iff.mp ha
        obtain ⟨g₂, hg₂, rfl⟩ := adj_γ₀_inr_iff.mp hb
        refine congrArg Sum.inr ?_
        have h1 := QuotientGroup.eq.mp (Sum.inr.inj hab)
        rw [Subgroup.mem_subgroupOf] at h1
        have h2 : (g₁ : G)⁻¹ * (g₂ : G) ∈ G₂ :=
          mem_of_map_mem hd.inj₁ hd.inter hd.le₁ hg₁ hg₂ (by simpa using h1)
        rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
        exact h2
  surj w hw := by
    rw [hd.Θ_γ₀] at hw
    cases w with
    | inl x => exact (not_adj_inl_inl hw).elim
    | inr y =>
      obtain ⟨h, hh, rfl⟩ := adj_γ₀_inr_iff.mp hw
      have hmem : (h : H) ∈ G₁.map θ := by rw [hd.map₁]; exact hh
      obtain ⟨k, hk, hkθ⟩ := hmem
      have hk0 : k ∈ G₁ ⊔ G₂ := Subgroup.mem_sup_left hk
      refine ⟨Sum.inr (((⟨k, hk0⟩ : ↥(G₁ ⊔ G₂))) : ↥(G₁ ⊔ G₂) ⧸ G₂.subgroupOf (G₁ ⊔ G₂)),
        adj_γ₀_inr_iff.mpr ⟨⟨k, hk0⟩, hk, rfl⟩, ?_⟩
      rw [hd.Θ_inr]
      exact congrArg Sum.inr (congrArg _ (Subtype.ext hkθ))

theorem isLocIso_γ₁ :
    IsLocIso (graph (G₁ ⊔ G₂) G₁ G₂) (graph (H₁ ⊔ H₂) H₁ H₂) hd.Θ (γ₁ (G₁ ⊔ G₂) G₁ G₂) where
  inj a b ha hb hab := by
    cases a with
    | inr y => exact (not_adj_inr_inr ha).elim
    | inl x₁ =>
      cases b with
      | inr y => exact (not_adj_inr_inr hb).elim
      | inl x₂ =>
        obtain ⟨g₁, hg₁, rfl⟩ := adj_γ₁_inl_iff.mp ha
        obtain ⟨g₂, hg₂, rfl⟩ := adj_γ₁_inl_iff.mp hb
        refine congrArg Sum.inl ?_
        have h1 := QuotientGroup.eq.mp (Sum.inl.inj hab)
        rw [Subgroup.mem_subgroupOf] at h1
        have hAB : (G₂ ⊓ G₁).map θ = H₂ ⊓ H₁ := by rw [inf_comm, hd.inter, inf_comm]
        have h2 : (g₁ : G)⁻¹ * (g₂ : G) ∈ G₁ :=
          mem_of_map_mem hd.inj₂ hAB hd.le₂ hg₁ hg₂ (by simpa using h1)
        rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
        exact h2
  surj w hw := by
    rw [hd.Θ_γ₁] at hw
    cases w with
    | inr y => exact (not_adj_inr_inr hw).elim
    | inl x =>
      obtain ⟨h, hh, rfl⟩ := adj_γ₁_inl_iff.mp hw
      have hmem : (h : H) ∈ G₂.map θ := by rw [hd.map₂]; exact hh
      obtain ⟨k, hk, hkθ⟩ := hmem
      have hk0 : k ∈ G₁ ⊔ G₂ := Subgroup.mem_sup_right hk
      refine ⟨Sum.inl (((⟨k, hk0⟩ : ↥(G₁ ⊔ G₂))) : ↥(G₁ ⊔ G₂) ⧸ G₁.subgroupOf (G₁ ⊔ G₂)),
        adj_γ₁_inl_iff.mpr ⟨⟨k, hk0⟩, hk, rfl⟩, ?_⟩
      rw [hd.Θ_inl]
      exact congrArg Sum.inl (congrArg _ (Subtype.ext hkθ))

theorem Θ_equivariant (g : ↥(G₁ ⊔ G₂)) (v : CosetGeom (G₁ ⊔ G₂) G₁ G₂) :
    hd.Θ (g • v) = hd.hom0 g • hd.Θ v := hd.Θ_smul g v

theorem isLocIso (v : CosetGeom (G₁ ⊔ G₂) G₁ G₂) :
    IsLocIso (graph (G₁ ⊔ G₂) G₁ G₂) (graph (H₁ ⊔ H₂) H₁ H₂) hd.Θ v := by
  cases hv : vtype v with
  | false =>
    obtain ⟨g, rfl⟩ := exists_smul_eq_γ₀ hv
    exact GraphCovering.isLocIso_smul hd.Θ_equivariant hd.isLocIso_γ₀ g
  | true =>
    obtain ⟨g, rfl⟩ := exists_smul_eq_γ₁ hv
    exact GraphCovering.isLocIso_smul hd.Θ_equivariant hd.isLocIso_γ₁ g

theorem Θ_adj {a b : CosetGeom (G₁ ⊔ G₂) G₁ G₂} (h : (graph (G₁ ⊔ G₂) G₁ G₂).Adj a b) :
    (graph (H₁ ⊔ H₂) H₁ H₂).Adj (hd.Θ a) (hd.Θ b) := by
  cases a with
  | inl x =>
    cases b with
    | inl x' => exact (not_adj_inl_inl h).elim
    | inr y =>
      obtain ⟨g, rfl, rfl⟩ := adj_inl_inr.mp h
      rw [hd.Θ_inl, hd.Θ_inr]
      exact adj_inl_inr.mpr ⟨hd.hom0 g, rfl, rfl⟩
  | inr y =>
    cases b with
    | inr y' => exact (not_adj_inr_inr h).elim
    | inl x =>
      obtain ⟨g, rfl, rfl⟩ := adj_inr_inl.mp h
      rw [hd.Θ_inl, hd.Θ_inr]
      exact adj_inr_inl.mpr ⟨hd.hom0 g, rfl, rfl⟩

theorem Θ_surjective : Function.Surjective hd.Θ := by
  intro v
  cases v with
  | inl x =>
    induction x using QuotientGroup.induction_on with
    | H h =>
      obtain ⟨g, rfl⟩ := hd.hom0_surjective h
      exact ⟨Sum.inl (g : _), hd.Θ_inl g⟩
  | inr y =>
    induction y using QuotientGroup.induction_on with
    | H h =>
      obtain ⟨g, rfl⟩ := hd.hom0_surjective h
      exact ⟨Sum.inr (g : _), hd.Θ_inr g⟩

theorem graphCovering :
    GraphCovering (graph (G₁ ⊔ G₂) G₁ G₂) (graph (H₁ ⊔ H₂) H₁ H₂) hd.Θ :=
  GraphCovering.of_isLocIso (fun _ _ h => hd.Θ_adj h) hd.Θ_surjective hd.isLocIso

theorem stabIso_γ₀ :
    GraphCovering.StabIso (θ := hd.Θ) (θG := hd.hom0) (γ₀ (G₁ ⊔ G₂) G₁ G₂) where
  equivariant := hd.Θ_smul
  inj gh hgh h1 := by
    have h2 : ((gh : ↥(G₁ ⊔ G₂)) : G) ∈ G₁ := by
      have h4 := mem_stab_of_smul_eq hgh
      rwa [stab_γ₀ (G₀ := G₁ ⊔ G₂) (G₂ := G₂) le_sup_left] at h4
    have h3 : θ (gh : G) = 1 := congrArg Subtype.val h1
    exact Subtype.ext (hd.inj₁ _ h2 h3)
  surj g' hg' := by
    have h2 : ((g' : ↥(H₁ ⊔ H₂)) : H) ∈ H₁ := by
      rw [hd.Θ_γ₀] at hg'
      have h4 := mem_stab_of_smul_eq hg'
      rwa [stab_γ₀ (G₀ := H₁ ⊔ H₂) (G₂ := H₂) le_sup_left] at h4
    have hmem : ((g' : ↥(H₁ ⊔ H₂)) : H) ∈ G₁.map θ := by rw [hd.map₁]; exact h2
    obtain ⟨k, hk, hkθ⟩ := hmem
    refine ⟨⟨k, Subgroup.mem_sup_left hk⟩, smul_γ₀_of_mem le_sup_left hk, Subtype.ext hkθ⟩

theorem stabIso_γ₁ :
    GraphCovering.StabIso (θ := hd.Θ) (θG := hd.hom0) (γ₁ (G₁ ⊔ G₂) G₁ G₂) where
  equivariant := hd.Θ_smul
  inj gh hgh h1 := by
    have h2 : ((gh : ↥(G₁ ⊔ G₂)) : G) ∈ G₂ := by
      have h4 := mem_stab_of_smul_eq hgh
      rwa [stab_γ₁ (G₀ := G₁ ⊔ G₂) (G₁ := G₁) le_sup_right] at h4
    have h3 : θ (gh : G) = 1 := congrArg Subtype.val h1
    exact Subtype.ext (hd.inj₂ _ h2 h3)
  surj g' hg' := by
    have h2 : ((g' : ↥(H₁ ⊔ H₂)) : H) ∈ H₂ := by
      rw [hd.Θ_γ₁] at hg'
      have h4 := mem_stab_of_smul_eq hg'
      rwa [stab_γ₁ (G₀ := H₁ ⊔ H₂) (G₁ := H₁) le_sup_right] at h4
    have hmem : ((g' : ↥(H₁ ⊔ H₂)) : H) ∈ G₂.map θ := by rw [hd.map₂]; exact h2
    obtain ⟨k, hk, hkθ⟩ := hmem
    refine ⟨⟨k, Subgroup.mem_sup_right hk⟩, smul_γ₁_of_mem le_sup_right hk, Subtype.ext hkθ⟩

theorem stabIso (uh : CosetGeom (G₁ ⊔ G₂) G₁ G₂) :
    GraphCovering.StabIso (θ := hd.Θ) (θG := hd.hom0) uh := by
  cases hv : vtype uh with
  | false =>
    obtain ⟨g, rfl⟩ := exists_smul_eq_γ₀ hv
    exact hd.stabIso_γ₀.smul g
  | true =>
    obtain ⟨g, rfl⟩ := exists_smul_eq_γ₁ hv
    exact hd.stabIso_γ₁.smul g

end CoverData

end CosetGeom

end CFSG.Quasithin
