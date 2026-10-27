module

public import CFSG.Quasithin.Background.F7Basic

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin.F7
open scoped Pointwise

variable {G : Type*} [Group G]

structure AmalgamHyp (G₀ G₁ G₂ T : Subgroup G) : Prop where
  gen : G₀ = G₁ ⊔ G₂
  charTwo : CharTwo G₁
  sylow₁ : IsSylowTwoOf T G₁
  sylow₂ : IsSylowTwoOf T G₂
  o2_trivial : pCoreOf 2 G₀ = ⊥

theorem AmalgamHyp.le₁ {G₀ G₁ G₂ T : Subgroup G} (h : AmalgamHyp G₀ G₁ G₂ T) : G₁ ≤ G₀ :=
  h.gen ▸ le_sup_left

theorem AmalgamHyp.le₂ {G₀ G₁ G₂ T : Subgroup G} (h : AmalgamHyp G₀ G₁ G₂ T) : G₂ ≤ G₀ :=
  h.gen ▸ le_sup_right

theorem AmalgamHyp.T_le {G₀ G₁ G₂ T : Subgroup G} (h : AmalgamHyp G₀ G₁ G₂ T) :
    T ≤ G₁ ⊓ G₂ := _root_.le_inf h.sylow₁.1 h.sylow₂.1

theorem AmalgamHyp.sylow_inf {G₀ G₁ G₂ T : Subgroup G} (h : AmalgamHyp G₀ G₁ G₂ T) :
    IsSylowTwoOf T (G₁ ⊓ G₂) :=
  isSylowTwoOf_mono_right h.sylow₁ h.T_le inf_le_left

abbrev CosetGeom (G₀ G₁ G₂ : Subgroup G) : Type _ :=
  (↥G₀ ⧸ G₁.subgroupOf G₀) ⊕ (↥G₀ ⧸ G₂.subgroupOf G₀)

namespace CosetGeom

variable {G₀ G₁ G₂ : Subgroup G}

@[expose] def Rel : CosetGeom G₀ G₁ G₂ → CosetGeom G₀ G₁ G₂ → Prop
  | Sum.inl x, Sum.inr y => ∃ g : G₀, (g : G₀ ⧸ G₁.subgroupOf G₀) = x ∧
      (g : G₀ ⧸ G₂.subgroupOf G₀) = y
  | Sum.inr y, Sum.inl x => ∃ g : G₀, (g : G₀ ⧸ G₁.subgroupOf G₀) = x ∧
      (g : G₀ ⧸ G₂.subgroupOf G₀) = y
  | _, _ => False

variable (G₀ G₁ G₂) in
@[expose] def graph : SimpleGraph (CosetGeom G₀ G₁ G₂) where
  Adj := Rel
  symm := ⟨by
    intro a b h
    cases a <;> cases b <;> exact h⟩
  loopless := ⟨by
    intro a h
    cases a <;> exact h⟩

theorem adj_inl_inr {x : G₀ ⧸ G₁.subgroupOf G₀} {y : G₀ ⧸ G₂.subgroupOf G₀} :
    (graph G₀ G₁ G₂).Adj (Sum.inl x) (Sum.inr y) ↔
      ∃ g : G₀, (g : G₀ ⧸ G₁.subgroupOf G₀) = x ∧ (g : G₀ ⧸ G₂.subgroupOf G₀) = y := Iff.rfl

theorem adj_inr_inl {x : G₀ ⧸ G₁.subgroupOf G₀} {y : G₀ ⧸ G₂.subgroupOf G₀} :
    (graph G₀ G₁ G₂).Adj (Sum.inr y) (Sum.inl x) ↔
      ∃ g : G₀, (g : G₀ ⧸ G₁.subgroupOf G₀) = x ∧ (g : G₀ ⧸ G₂.subgroupOf G₀) = y := Iff.rfl

theorem not_adj_inl_inl {x x' : G₀ ⧸ G₁.subgroupOf G₀} :
    ¬ (graph G₀ G₁ G₂).Adj (Sum.inl x) (Sum.inl x') := fun h => h

theorem not_adj_inr_inr {y y' : G₀ ⧸ G₂.subgroupOf G₀} :
    ¬ (graph G₀ G₁ G₂).Adj (Sum.inr y) (Sum.inr y') := fun h => h

@[expose] noncomputable def dist (γ δ : CosetGeom G₀ G₁ G₂) : ℕ := (graph G₀ G₁ G₂).dist γ δ

variable (G₀ G₁ G₂) in
@[expose] def γ₀ : CosetGeom G₀ G₁ G₂ := Sum.inl (1 : ↥G₀)

variable (G₀ G₁ G₂) in
@[expose] def γ₁ : CosetGeom G₀ G₁ G₂ := Sum.inr (1 : ↥G₀)

@[expose] def vtype : CosetGeom G₀ G₁ G₂ → Bool
  | Sum.inl _ => false
  | Sum.inr _ => true

variable (G₀ G₁ G₂) in
@[expose] def Γ0 : Set (CosetGeom G₀ G₁ G₂) := Set.range Sum.inl

variable (G₀ G₁ G₂) in
@[expose] def Γ1 : Set (CosetGeom G₀ G₁ G₂) := Set.range Sum.inr

@[expose] def sphere (i : ℕ) (γ : CosetGeom G₀ G₁ G₂) : Set (CosetGeom G₀ G₁ G₂) := {δ | dist γ δ = i}

@[expose] def nbrs (γ : CosetGeom G₀ G₁ G₂) : Set (CosetGeom G₀ G₁ G₂) := {δ | (graph G₀ G₁ G₂).Adj γ δ}

@[expose] def ballLT (i : ℕ) (γ : CosetGeom G₀ G₁ G₂) : Set (CosetGeom G₀ G₁ G₂) := {δ | dist γ δ < i}

@[expose] def ballLE (i : ℕ) (γ : CosetGeom G₀ G₁ G₂) : Set (CosetGeom G₀ G₁ G₂) := {δ | dist γ δ ≤ i}

theorem smul_coe_quot (g k : G₀) (H : Subgroup G₀) :
    g • (k : G₀ ⧸ H) = ((g * k : G₀) : G₀ ⧸ H) := rfl

theorem smul_inl (g : G₀) (x : G₀ ⧸ G₁.subgroupOf G₀) :
    g • (Sum.inl x : CosetGeom G₀ G₁ G₂) = Sum.inl (g • x) := rfl

theorem smul_inr (g : G₀) (y : G₀ ⧸ G₂.subgroupOf G₀) :
    g • (Sum.inr y : CosetGeom G₀ G₁ G₂) = Sum.inr (g • y) := rfl

theorem smul_adj (g : G₀) {u v : CosetGeom G₀ G₁ G₂} :
    (graph G₀ G₁ G₂).Adj (g • u) (g • v) ↔ (graph G₀ G₁ G₂).Adj u v := by
  have key : ∀ {x : G₀ ⧸ G₁.subgroupOf G₀} {y : G₀ ⧸ G₂.subgroupOf G₀},
      (∃ k : G₀, (k : G₀ ⧸ G₁.subgroupOf G₀) = g • x ∧ (k : G₀ ⧸ G₂.subgroupOf G₀) = g • y) ↔
        ∃ k : G₀, (k : G₀ ⧸ G₁.subgroupOf G₀) = x ∧ (k : G₀ ⧸ G₂.subgroupOf G₀) = y := by
    intro x y
    constructor
    · rintro ⟨k, h1, h2⟩
      refine ⟨g⁻¹ * k, ?_, ?_⟩
      · rw [← smul_coe_quot, h1, inv_smul_smul]
      · rw [← smul_coe_quot, h2, inv_smul_smul]
    · rintro ⟨k, h1, h2⟩
      refine ⟨g * k, ?_, ?_⟩
      · rw [← smul_coe_quot, h1]
      · rw [← smul_coe_quot, h2]
  cases u <;> cases v
  · exact iff_of_false (not_adj_inl_inl) (not_adj_inl_inl)
  · exact key
  · exact key
  · exact iff_of_false (not_adj_inr_inr) (not_adj_inr_inr)

theorem vtype_smul (g : G₀) (γ : CosetGeom G₀ G₁ G₂) : vtype (g • γ) = vtype γ := by
  cases γ <;> rfl

theorem vtype_ne_of_adj {u v : CosetGeom G₀ G₁ G₂} (h : (graph G₀ G₁ G₂).Adj u v) :
    vtype u ≠ vtype v := by
  cases u <;> cases v
  · exact (not_adj_inl_inl h).elim
  · simp [vtype]
  · simp [vtype]
  · exact (not_adj_inr_inr h).elim

theorem edist_smul_le (g : G₀) (u v : CosetGeom G₀ G₁ G₂) :
    (graph G₀ G₁ G₂).edist (g • u) (g • v) ≤ (graph G₀ G₁ G₂).edist u v := by
  by_cases h : (graph G₀ G₁ G₂).edist u v = ⊤
  · rw [h]; exact le_top
  · obtain ⟨p, hp⟩ := SimpleGraph.exists_walk_of_edist_ne_top h
    let φ : graph G₀ G₁ G₂ →g graph G₀ G₁ G₂ :=
      ⟨fun w => g • w, fun {_ _} hab => (smul_adj g).mpr hab⟩
    have := SimpleGraph.edist_le (p.map φ)
    rw [SimpleGraph.Walk.length_map, hp] at this
    exact this

theorem edist_smul (g : G₀) (u v : CosetGeom G₀ G₁ G₂) :
    (graph G₀ G₁ G₂).edist (g • u) (g • v) = (graph G₀ G₁ G₂).edist u v := by
  refine le_antisymm (edist_smul_le g u v) ?_
  have := edist_smul_le g⁻¹ (g • u) (g • v)
  simpa using this

theorem dist_smul (g : G₀) (u v : CosetGeom G₀ G₁ G₂) : dist (g • u) (g • v) = dist u v := by
  unfold dist SimpleGraph.dist
  rw [edist_smul]

theorem dist_comm (u v : CosetGeom G₀ G₁ G₂) : dist u v = dist v u :=
  SimpleGraph.dist_comm

theorem dist_self (u : CosetGeom G₀ G₁ G₂) : dist u u = 0 := SimpleGraph.dist_self

theorem dist_eq_one_iff_adj {u v : CosetGeom G₀ G₁ G₂} :
    dist u v = 1 ↔ (graph G₀ G₁ G₂).Adj u v := SimpleGraph.dist_eq_one_iff_adj

theorem dist_triangle_of_adj {u v : CosetGeom G₀ G₁ G₂} (h : (graph G₀ G₁ G₂).Adj u v)
    (w : CosetGeom G₀ G₁ G₂) : dist u w ≤ dist u v + dist v w :=
  h.reachable.dist_triangle_left w

theorem smul_γ₀ (g : G₀) :
    g • γ₀ G₀ G₁ G₂ = Sum.inl (g : G₀ ⧸ G₁.subgroupOf G₀) := by
  simp [γ₀]

theorem smul_γ₁ (g : G₀) :
    g • γ₁ G₀ G₁ G₂ = Sum.inr (g : G₀ ⧸ G₂.subgroupOf G₀) := by
  simp [γ₁]

theorem exists_smul_γ₀ (x : G₀ ⧸ G₁.subgroupOf G₀) :
    ∃ g : G₀, g • γ₀ G₀ G₁ G₂ = Sum.inl x := by
  induction x using QuotientGroup.induction_on with
  | H a => exact ⟨a, by simp [γ₀]⟩

theorem exists_smul_γ₁ (y : G₀ ⧸ G₂.subgroupOf G₀) :
    ∃ g : G₀, g • γ₁ G₀ G₁ G₂ = Sum.inr y := by
  induction y using QuotientGroup.induction_on with
  | H a => exact ⟨a, by simp [γ₁]⟩

theorem exists_smul_eq_γ₀ {γ : CosetGeom G₀ G₁ G₂} (h : vtype γ = false) :
    ∃ g : G₀, γ = g • γ₀ G₀ G₁ G₂ := by
  cases γ with
  | inl x => obtain ⟨g, hg⟩ := exists_smul_γ₀ (G₂ := G₂) x; exact ⟨g, hg.symm⟩
  | inr y => simp [vtype] at h

theorem exists_smul_eq_γ₁ {γ : CosetGeom G₀ G₁ G₂} (h : vtype γ = true) :
    ∃ g : G₀, γ = g • γ₁ G₀ G₁ G₂ := by
  cases γ with
  | inl x => simp [vtype] at h
  | inr y => obtain ⟨g, hg⟩ := exists_smul_γ₁ (G₁ := G₁) y; exact ⟨g, hg.symm⟩

theorem orbit_γ₀_eq_Γ0 : MulAction.orbit G₀ (γ₀ G₀ G₁ G₂) = Γ0 G₀ G₁ G₂ := by
  ext v
  constructor
  · rintro ⟨g, rfl⟩
    exact ⟨_, rfl⟩
  · rintro ⟨x, rfl⟩
    exact exists_smul_γ₀ x

theorem orbit_γ₁_eq_Γ1 : MulAction.orbit G₀ (γ₁ G₀ G₁ G₂) = Γ1 G₀ G₁ G₂ := by
  ext v
  constructor
  · rintro ⟨g, rfl⟩
    exact ⟨_, rfl⟩
  · rintro ⟨x, rfl⟩
    exact exists_smul_γ₁ x

@[expose] def stab (γ : CosetGeom G₀ G₁ G₂) : Subgroup G := (MulAction.stabilizer ↥G₀ γ).map G₀.subtype

theorem mem_stab {γ : CosetGeom G₀ G₁ G₂} {x : G} :
    x ∈ stab γ ↔ ∃ h : x ∈ G₀, (⟨x, h⟩ : ↥G₀) • γ = γ := by
  constructor
  · rintro ⟨g, hg, rfl⟩
    exact ⟨g.2, hg⟩
  · rintro ⟨h, hx⟩
    exact ⟨⟨x, h⟩, hx, rfl⟩

theorem stab_le (γ : CosetGeom G₀ G₁ G₂) : stab γ ≤ G₀ := Subgroup.map_subtype_le _

theorem smul_eq_of_mem_stab {γ : CosetGeom G₀ G₁ G₂} {g : G₀} (h : (g : G) ∈ stab γ) :
    g • γ = γ := by
  obtain ⟨h', hx⟩ := mem_stab.mp h
  exact hx

theorem mem_stab_of_smul_eq {γ : CosetGeom G₀ G₁ G₂} {g : G₀} (h : g • γ = γ) :
    (g : G) ∈ stab γ := mem_stab.mpr ⟨g.2, h⟩

theorem stab_smul (g : G₀) (γ : CosetGeom G₀ G₁ G₂) :
    stab (g • γ) = conjSub (g : G) (stab γ) := by
  ext x
  rw [mem_conjSub, mem_stab, mem_stab]
  constructor
  · rintro ⟨h, hx⟩
    have h' : (g : G)⁻¹ * x * g ∈ G₀ := G₀.mul_mem (G₀.mul_mem (G₀.inv_mem g.2) h) g.2
    refine ⟨h', ?_⟩
    have e : (⟨(g : G)⁻¹ * x * g, h'⟩ : ↥G₀) = g⁻¹ * ⟨x, h⟩ * g := rfl
    rw [e, mul_smul, mul_smul, hx, inv_smul_smul]
  · rintro ⟨h', hx⟩
    have h : x ∈ G₀ := by
      have := G₀.mul_mem (G₀.mul_mem g.2 h') (G₀.inv_mem g.2)
      simpa [mul_assoc] using this
    refine ⟨h, ?_⟩
    have e : (⟨x, h⟩ : ↥G₀) = g * ⟨(g : G)⁻¹ * x * g, h'⟩ * g⁻¹ := by
      apply Subtype.ext; simp [mul_assoc]
    rw [e, mul_smul, mul_smul, inv_smul_smul, hx]

theorem stab_γ₀ (h₁ : G₁ ≤ G₀) : stab (γ₀ G₀ G₁ G₂) = G₁ := by
  ext x
  rw [mem_stab]
  constructor
  · rintro ⟨h, hx⟩
    rw [smul_γ₀] at hx
    have := Sum.inl.inj hx
    rw [QuotientGroup.eq, mul_one, inv_mem_iff, Subgroup.mem_subgroupOf] at this
    exact this
  · intro hx
    refine ⟨h₁ hx, ?_⟩
    rw [smul_γ₀]
    refine congrArg Sum.inl ?_
    rw [QuotientGroup.eq, mul_one, inv_mem_iff, Subgroup.mem_subgroupOf]
    exact hx

theorem stab_γ₁ (h₂ : G₂ ≤ G₀) : stab (γ₁ G₀ G₁ G₂) = G₂ := by
  ext x
  rw [mem_stab]
  constructor
  · rintro ⟨h, hx⟩
    rw [smul_γ₁] at hx
    have := Sum.inr.inj hx
    rw [QuotientGroup.eq, mul_one, inv_mem_iff, Subgroup.mem_subgroupOf] at this
    exact this
  · intro hx
    refine ⟨h₂ hx, ?_⟩
    rw [smul_γ₁]
    refine congrArg Sum.inr ?_
    rw [QuotientGroup.eq, mul_one, inv_mem_iff, Subgroup.mem_subgroupOf]
    exact hx

theorem mem_normalizer_of_conjSub_eq {g : G} {N : Subgroup G} (h : conjSub g N = N) :
    g ∈ Subgroup.normalizer (N : Set G) :=
  mem_normalizer_of_conj_le h.le (by
    have := conjSub_conjSub_inv g N
    rw [h] at this
    exact this.le)

@[expose] noncomputable def ballStab (n : ℕ) (γ : CosetGeom G₀ G₁ G₂) : Subgroup G :=
  ⨅ (δ : CosetGeom G₀ G₁ G₂) (_ : dist γ δ ≤ n), stab δ

theorem mem_ballStab {n : ℕ} {γ : CosetGeom G₀ G₁ G₂} {x : G} :
    x ∈ ballStab n γ ↔ ∀ δ, dist γ δ ≤ n → x ∈ stab δ := by
  simp [ballStab, Subgroup.mem_iInf]

theorem ballStab_le_stab (n : ℕ) (γ : CosetGeom G₀ G₁ G₂) : ballStab n γ ≤ stab γ := fun _ hx =>
  mem_ballStab.mp hx γ (by simp [dist_self])

theorem ballStab_antitone (γ : CosetGeom G₀ G₁ G₂) : Antitone fun n => ballStab n γ :=
  fun _ _ hmn _ hx => mem_ballStab.mpr fun δ hδ => mem_ballStab.mp hx δ (hδ.trans hmn)

theorem ballStab_le_of_le {m n : ℕ} (h : m ≤ n) (γ : CosetGeom G₀ G₁ G₂) :
    ballStab n γ ≤ ballStab m γ := ballStab_antitone γ h

theorem ballStab_le_stab_of_dist_le {n : ℕ} {γ δ : CosetGeom G₀ G₁ G₂} (h : dist γ δ ≤ n) :
    ballStab n γ ≤ stab δ := fun _ hx => mem_ballStab.mp hx δ h

theorem ballStab_smul (g : G₀) (n : ℕ) (γ : CosetGeom G₀ G₁ G₂) :
    ballStab n (g • γ) = conjSub (g : G) (ballStab n γ) := by
  ext x
  rw [mem_conjSub, mem_ballStab, mem_ballStab]
  constructor
  · intro h δ hδ
    have := h (g • δ) (by rwa [dist_smul])
    rw [stab_smul, mem_conjSub] at this
    exact this
  · intro h δ hδ
    obtain ⟨δ', rfl⟩ : ∃ δ', δ = g • δ' := ⟨g⁻¹ • δ, by simp⟩
    rw [dist_smul] at hδ
    rw [stab_smul, mem_conjSub]
    exact h δ' hδ

theorem ballStab_normal (n : ℕ) (γ : CosetGeom G₀ G₁ G₂) :
    ballStab n γ ≤ stab γ ∧ ((ballStab n γ).subgroupOf (stab γ)).Normal := by
  refine ⟨ballStab_le_stab n γ, ?_⟩
  rw [Subgroup.normal_subgroupOf_iff_le_normalizer (ballStab_le_stab n γ)]
  intro x hx
  obtain ⟨h, hxγ⟩ := mem_stab.mp hx
  apply mem_normalizer_of_conjSub_eq
  have := ballStab_smul (⟨x, h⟩ : ↥G₀) n γ
  rw [hxγ] at this
  exact this.symm

theorem le_normalizer_ballStab (n : ℕ) (γ : CosetGeom G₀ G₁ G₂) :
    stab γ ≤ Subgroup.normalizer (ballStab n γ : Set G) :=
  (Subgroup.normal_subgroupOf_iff_le_normalizer (ballStab_le_stab n γ)).mp
    (ballStab_normal n γ).2

theorem ballStab_succ_le_of_adj {α β : CosetGeom G₀ G₁ G₂} (h : (graph G₀ G₁ G₂).Adj α β)
    (n : ℕ) : ballStab (n + 1) α ≤ ballStab n β := by
  intro x hx
  refine mem_ballStab.mpr fun δ hδ => mem_ballStab.mp hx δ ?_
  have h1 : dist α β = 1 := dist_eq_one_iff_adj.mpr h
  have := dist_triangle_of_adj h δ
  omega

theorem reachable_smul (g : G₀) {u v : CosetGeom G₀ G₁ G₂}
    (h : (graph G₀ G₁ G₂).Reachable u v) : (graph G₀ G₁ G₂).Reachable (g • u) (g • v) := by
  obtain ⟨p⟩ := h
  exact ⟨p.map ⟨fun w => g • w, fun {_ _} hab => (smul_adj g).mpr hab⟩⟩

theorem adj_γ₀_γ₁ : (graph G₀ G₁ G₂).Adj (γ₀ G₀ G₁ G₂) (γ₁ G₀ G₁ G₂) := ⟨1, rfl, rfl⟩

theorem smul_γ₀_of_mem {x : G} (h₁ : G₁ ≤ G₀) (hx : x ∈ G₁) :
    (⟨x, h₁ hx⟩ : ↥G₀) • γ₀ G₀ G₁ G₂ = γ₀ G₀ G₁ G₂ :=
  smul_eq_of_mem_stab (by rw [stab_γ₀ h₁]; exact hx)

theorem smul_γ₁_of_mem {x : G} (h₂ : G₂ ≤ G₀) (hx : x ∈ G₂) :
    (⟨x, h₂ hx⟩ : ↥G₀) • γ₁ G₀ G₁ G₂ = γ₁ G₀ G₁ G₂ :=
  smul_eq_of_mem_stab (by rw [stab_γ₁ h₂]; exact hx)

theorem vtype_γ₀ : vtype (γ₀ G₀ G₁ G₂) = false := rfl

theorem vtype_γ₁ : vtype (γ₁ G₀ G₁ G₂) = true := rfl

theorem smul_γ₀_ne_smul_γ₁ (g g' : G₀) : g • γ₀ G₀ G₁ G₂ ≠ g' • γ₁ G₀ G₁ G₂ := by
  intro h
  have := congrArg vtype h
  rw [vtype_smul, vtype_smul, vtype_γ₀, vtype_γ₁] at this
  exact Bool.false_ne_true this

theorem connected (hG : G₀ = G₁ ⊔ G₂) : (graph G₀ G₁ G₂).Connected := by
  have h₁ : G₁ ≤ G₀ := hG ▸ le_sup_left
  have h₂ : G₂ ≤ G₀ := hG ▸ le_sup_right
  have key : ∀ x ∈ G₁ ⊔ G₂, ∃ h : x ∈ G₀,
      (graph G₀ G₁ G₂).Reachable (γ₀ G₀ G₁ G₂) ((⟨x, h⟩ : ↥G₀) • γ₀ G₀ G₁ G₂) ∧
      (graph G₀ G₁ G₂).Reachable (γ₀ G₀ G₁ G₂) ((⟨x, h⟩ : ↥G₀) • γ₁ G₀ G₁ G₂) := by
    intro x hx
    rw [Subgroup.sup_eq_closure] at hx
    induction hx using Subgroup.closure_induction with
    | mem x hx =>
      rcases hx with hx | hx
      · refine ⟨h₁ hx, ?_, ?_⟩
        · rw [smul_γ₀_of_mem h₁ hx]
        · have h := (smul_adj (⟨x, h₁ hx⟩ : ↥G₀)).mpr
            (adj_γ₀_γ₁ (G₀ := G₀) (G₁ := G₁) (G₂ := G₂))
          rw [smul_γ₀_of_mem h₁ hx] at h
          exact h.reachable
      · refine ⟨h₂ hx, ?_, ?_⟩
        · have h := (smul_adj (⟨x, h₂ hx⟩ : ↥G₀)).mpr
            (adj_γ₀_γ₁ (G₀ := G₀) (G₁ := G₁) (G₂ := G₂))
          rw [smul_γ₁_of_mem h₂ hx] at h
          exact (adj_γ₀_γ₁ (G₀ := G₀) (G₁ := G₁) (G₂ := G₂)).reachable.trans h.symm.reachable
        · rw [smul_γ₁_of_mem h₂ hx]
          exact (adj_γ₀_γ₁ (G₀ := G₀) (G₁ := G₁) (G₂ := G₂)).reachable
    | one =>
      have e : (⟨1, G₀.one_mem⟩ : ↥G₀) = 1 := rfl
      refine ⟨G₀.one_mem, ?_, ?_⟩
      · simp only [e, one_smul]; exact SimpleGraph.Reachable.refl _
      · simp only [e, one_smul]; exact (adj_γ₀_γ₁ (G₀ := G₀) (G₁ := G₁) (G₂ := G₂)).reachable
    | mul x y hx hy ihx ihy =>
      obtain ⟨hx', rx0, rx1⟩ := ihx
      obtain ⟨hy', ry0, ry1⟩ := ihy
      refine ⟨G₀.mul_mem hx' hy', ?_, ?_⟩
      · have e : (⟨x * y, G₀.mul_mem hx' hy'⟩ : ↥G₀) = ⟨x, hx'⟩ * ⟨y, hy'⟩ := rfl
        rw [e, mul_smul]
        exact rx0.trans (reachable_smul ⟨x, hx'⟩ ry0)
      · have e : (⟨x * y, G₀.mul_mem hx' hy'⟩ : ↥G₀) = ⟨x, hx'⟩ * ⟨y, hy'⟩ := rfl
        rw [e, mul_smul]
        exact rx0.trans (reachable_smul ⟨x, hx'⟩ ry1)
    | inv x hx ih =>
      obtain ⟨hx', rx0, rx1⟩ := ih
      refine ⟨G₀.inv_mem hx', ?_, ?_⟩
      · have e : (⟨x⁻¹, G₀.inv_mem hx'⟩ : ↥G₀) = (⟨x, hx'⟩ : ↥G₀)⁻¹ := rfl
        have := reachable_smul (⟨x, hx'⟩ : ↥G₀)⁻¹ rx0
        rw [inv_smul_smul] at this
        rw [e]
        exact this.symm
      · have e : (⟨x⁻¹, G₀.inv_mem hx'⟩ : ↥G₀) = (⟨x, hx'⟩ : ↥G₀)⁻¹ := rfl
        have h1 := reachable_smul (⟨x, hx'⟩ : ↥G₀)⁻¹ rx1
        rw [inv_smul_smul] at h1
        have h2 : (graph G₀ G₁ G₂).Reachable (γ₀ G₀ G₁ G₂)
            ((⟨x, hx'⟩ : ↥G₀)⁻¹ • γ₀ G₀ G₁ G₂) := by
          have := reachable_smul (⟨x, hx'⟩ : ↥G₀)⁻¹ rx0
          rw [inv_smul_smul] at this
          exact this.symm
        rw [e]
        exact h2.trans (reachable_smul _ (adj_γ₀_γ₁ (G₀ := G₀) (G₁ := G₁) (G₂ := G₂)).reachable)
  rw [SimpleGraph.connected_iff_exists_forall_reachable]
  refine ⟨γ₀ G₀ G₁ G₂, fun v => ?_⟩
  have hmem : ∀ g : ↥G₀, ∃ h : (g : G) ∈ G₀,
      (graph G₀ G₁ G₂).Reachable (γ₀ G₀ G₁ G₂) ((⟨g, h⟩ : ↥G₀) • γ₀ G₀ G₁ G₂) ∧
      (graph G₀ G₁ G₂).Reachable (γ₀ G₀ G₁ G₂) ((⟨g, h⟩ : ↥G₀) • γ₁ G₀ G₁ G₂) :=
    fun g => key g.1 (by rw [← hG]; exact g.2)
  cases hv : vtype v with
  | false =>
    obtain ⟨g, hg⟩ := exists_smul_eq_γ₀ hv
    obtain ⟨_, r0, _⟩ := hmem g
    rw [hg]; exact r0
  | true =>
    obtain ⟨g, hg⟩ := exists_smul_eq_γ₁ hv
    obtain ⟨_, _, r1⟩ := hmem g
    rw [hg]; exact r1

theorem dist_le_one_iff (hG : G₀ = G₁ ⊔ G₂) {u v : CosetGeom G₀ G₁ G₂} :
    dist u v ≤ 1 ↔ u = v ∨ (graph G₀ G₁ G₂).Adj u v := by
  have hc := connected hG
  constructor
  · intro h
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp h with h0 | h1
    · left; exact (hc.dist_eq_zero_iff).mp h0
    · right; exact dist_eq_one_iff_adj.mp h1
  · rintro (rfl | h)
    · simp [dist_self]
    · exact (dist_eq_one_iff_adj.mpr h).le

theorem dist_eq_zero_iff (hG : G₀ = G₁ ⊔ G₂) {u v : CosetGeom G₀ G₁ G₂} :
    dist u v = 0 ↔ u = v := (connected hG).dist_eq_zero_iff

theorem exists_smul_edge {u v : CosetGeom G₀ G₁ G₂} (h : (graph G₀ G₁ G₂).Adj u v) :
    ∃ g : G₀, (g • γ₀ G₀ G₁ G₂ = u ∧ g • γ₁ G₀ G₁ G₂ = v) ∨
      (g • γ₀ G₀ G₁ G₂ = v ∧ g • γ₁ G₀ G₁ G₂ = u) := by
  cases u with
  | inl x =>
    cases v with
    | inl x' => exact (not_adj_inl_inl h).elim
    | inr y =>
      obtain ⟨k, hk1, hk2⟩ := adj_inl_inr.mp h
      refine ⟨k, Or.inl ⟨?_, ?_⟩⟩
      · rw [smul_γ₀, hk1]
      · rw [smul_γ₁, hk2]
  | inr y =>
    cases v with
    | inl x =>
      obtain ⟨k, hk1, hk2⟩ := adj_inr_inl.mp h
      refine ⟨k, Or.inr ⟨?_, ?_⟩⟩
      · rw [smul_γ₀, hk1]
      · rw [smul_γ₁, hk2]
    | inr y' => exact (not_adj_inr_inr h).elim

theorem exists_smul_edge_set {u v : CosetGeom G₀ G₁ G₂} (h : (graph G₀ G₁ G₂).Adj u v) :
    ∃ g : G₀, g • ({γ₀ G₀ G₁ G₂, γ₁ G₀ G₁ G₂} : Set (CosetGeom G₀ G₁ G₂)) = {u, v} := by
  obtain ⟨g, hg | hg⟩ := exists_smul_edge h
  · refine ⟨g, ?_⟩
    rw [Set.smul_set_insert, Set.smul_set_singleton, hg.1, hg.2]
  · refine ⟨g, ?_⟩
    rw [Set.smul_set_insert, Set.smul_set_singleton, hg.1, hg.2, Set.pair_comm]

theorem smul_edge_eq_iff (h₁ : G₁ ≤ G₀) (h₂ : G₂ ≤ G₀) (g : G₀) :
    g • ({γ₀ G₀ G₁ G₂, γ₁ G₀ G₁ G₂} : Set (CosetGeom G₀ G₁ G₂)) = {γ₀ G₀ G₁ G₂, γ₁ G₀ G₁ G₂} ↔
      (g : G) ∈ G₁ ⊓ G₂ := by
  rw [Set.smul_set_insert, Set.smul_set_singleton, Set.pair_eq_pair_iff]
  constructor
  · rintro (⟨h1, h2⟩ | ⟨h1, _⟩)
    · have a1 : (g : G) ∈ stab (γ₀ G₀ G₁ G₂) := mem_stab_of_smul_eq h1
      have a2 : (g : G) ∈ stab (γ₁ G₀ G₁ G₂) := mem_stab_of_smul_eq h2
      rw [stab_γ₀ h₁] at a1
      rw [stab_γ₁ h₂] at a2
      exact ⟨a1, a2⟩
    · exact (smul_γ₀_ne_smul_γ₁ g 1 (by simpa using h1)).elim
  · rintro ⟨a1, a2⟩
    left
    exact ⟨smul_γ₀_of_mem h₁ a1, smul_γ₁_of_mem h₂ a2⟩

theorem exists_stab_smul_eq {γ δ δ' : CosetGeom G₀ G₁ G₂} (h : (graph G₀ G₁ G₂).Adj γ δ)
    (h' : (graph G₀ G₁ G₂).Adj γ δ') : ∃ g : G₀, g • γ = γ ∧ g • δ = δ' := by
  obtain ⟨g, hg | hg⟩ := exists_smul_edge h
  · obtain ⟨g', hg' | hg'⟩ := exists_smul_edge h'
    · have e1 : g⁻¹ • γ = γ₀ G₀ G₁ G₂ := by rw [← hg.1, inv_smul_smul]
      have e2 : g⁻¹ • δ = γ₁ G₀ G₁ G₂ := by rw [← hg.2, inv_smul_smul]
      exact ⟨g' * g⁻¹, by rw [mul_smul, e1, hg'.1], by rw [mul_smul, e2, hg'.2]⟩
    · exact (smul_γ₀_ne_smul_γ₁ g g' (hg.1.trans hg'.2.symm)).elim
  · obtain ⟨g', hg' | hg'⟩ := exists_smul_edge h'
    · exact (smul_γ₀_ne_smul_γ₁ g' g (hg'.1.trans hg.2.symm)).elim
    · have e1 : g⁻¹ • γ = γ₁ G₀ G₁ G₂ := by rw [← hg.2, inv_smul_smul]
      have e2 : g⁻¹ • δ = γ₀ G₀ G₁ G₂ := by rw [← hg.1, inv_smul_smul]
      exact ⟨g' * g⁻¹, by rw [mul_smul, e1, hg'.2], by rw [mul_smul, e2, hg'.1]⟩

theorem stab_transitive_on_nbrs {γ δ δ' : CosetGeom G₀ G₁ G₂} (h : δ ∈ nbrs γ) (h' : δ' ∈ nbrs γ) :
    ∃ g : G₀, (g : G) ∈ stab γ ∧ g • δ = δ' := by
  obtain ⟨g, hg1, hg2⟩ := exists_stab_smul_eq h h'
  exact ⟨g, mem_stab_of_smul_eq hg1, hg2⟩

theorem exists_adj (γ : CosetGeom G₀ G₁ G₂) : ∃ δ, (graph G₀ G₁ G₂).Adj γ δ := by
  cases hv : vtype γ with
  | false =>
    obtain ⟨g, hg⟩ := exists_smul_eq_γ₀ hv
    exact ⟨g • γ₁ G₀ G₁ G₂, by rw [hg]; exact (smul_adj g).mpr adj_γ₀_γ₁⟩
  | true =>
    obtain ⟨g, hg⟩ := exists_smul_eq_γ₁ hv
    exact ⟨g • γ₀ G₀ G₁ G₂, by rw [hg]; exact (smul_adj g).mpr adj_γ₀_γ₁.symm⟩

theorem exists_adj_dist_eq (hG : G₀ = G₁ ⊔ G₂) {α δ : CosetGeom G₀ G₁ G₂} {d : ℕ}
    (h : dist α δ = d + 1) : ∃ β, (graph G₀ G₁ G₂).Adj δ β ∧ dist α β = d := by
  have hc := connected hG
  obtain ⟨p, hp⟩ := hc.exists_walk_length_eq_dist α δ
  have hlen : p.reverse.length = d + 1 := by
    rw [SimpleGraph.Walk.length_reverse, hp]; exact h
  cases hq : p.reverse with
  | nil => rw [hq] at hlen; simp at hlen
  | cons hadj q =>
    rw [hq, SimpleGraph.Walk.length_cons] at hlen
    have hq' : q.length = d := by omega
    rename_i β
    refine ⟨β, hadj, ?_⟩
    have h1 : (graph G₀ G₁ G₂).dist β α ≤ d := by
      have := SimpleGraph.dist_le q
      omega
    have h2 : dist α δ ≤ dist α β + dist β δ := hc.dist_triangle
    have h3 : dist β δ = 1 := by
      rw [dist_comm]; exact dist_eq_one_iff_adj.mpr hadj
    have h4 : dist α β = (graph G₀ G₁ G₂).dist α β := rfl
    have h5 : (graph G₀ G₁ G₂).dist β α = (graph G₀ G₁ G₂).dist α β := SimpleGraph.dist_comm
    omega

theorem ballStab_one_eq_coreIn (hG : G₀ = G₁ ⊔ G₂) {α β : CosetGeom G₀ G₁ G₂}
    (h : (graph G₀ G₁ G₂).Adj α β) :
    ballStab 1 α = coreIn (stab α ⊓ stab β) (stab α) := by
  ext x
  rw [mem_ballStab, mem_coreIn]
  constructor
  · intro hx
    have hxα : x ∈ stab α := hx α (by simp [dist_self])
    refine ⟨hxα, fun h' hh' => ⟨?_, ?_⟩⟩
    · exact (stab α).mul_mem ((stab α).mul_mem ((stab α).inv_mem hh') hxα) hh'
    · obtain ⟨hmem, hfix⟩ := mem_stab.mp hh'
      have hadj : (graph G₀ G₁ G₂).Adj α ((⟨h', hmem⟩ : ↥G₀) • β) := by
        have := (smul_adj (⟨h', hmem⟩ : ↥G₀)).mpr h
        rwa [hfix] at this
      have hd : dist α ((⟨h', hmem⟩ : ↥G₀) • β) ≤ 1 := (dist_eq_one_iff_adj.mpr hadj).le
      have := hx _ hd
      rw [stab_smul, mem_conjSub] at this
      exact this
  · rintro ⟨hxα, hcore⟩ δ hδ
    rcases (dist_le_one_iff hG).mp hδ with rfl | hδ'
    · exact hxα
    · obtain ⟨g, hg1, hg2⟩ := exists_stab_smul_eq h hδ'
      have hgmem : (g : G) ∈ stab α := mem_stab_of_smul_eq hg1
      have := (hcore (g : G) hgmem).2
      rw [← hg2, stab_smul, mem_conjSub]
      exact this

theorem ballStab_one_γ₀ (hG : G₀ = G₁ ⊔ G₂) :
    ballStab 1 (γ₀ G₀ G₁ G₂) = coreIn (G₁ ⊓ G₂) G₁ ∧
      IsGreatest {N : Subgroup G | N ≤ G₁ ⊓ G₂ ∧ G₁ ≤ Subgroup.normalizer (N : Set G)}
        (ballStab 1 (γ₀ G₀ G₁ G₂)) := by
  have h₁ : G₁ ≤ G₀ := hG ▸ le_sup_left
  have h₂ : G₂ ≤ G₀ := hG ▸ le_sup_right
  have key : ballStab 1 (γ₀ G₀ G₁ G₂) = coreIn (G₁ ⊓ G₂) G₁ := by
    rw [ballStab_one_eq_coreIn hG (adj_γ₀_γ₁ (G₀ := G₀) (G₁ := G₁) (G₂ := G₂)), stab_γ₀ h₁,
      stab_γ₁ h₂]
  refine ⟨key, ?_, ?_⟩
  · rw [key]; exact ⟨coreIn_le_right _ _, le_normalizer_coreIn _ _⟩
  · rintro N ⟨hN1, hN2⟩
    rw [key]
    exact le_coreIn (hN1.trans inf_le_left) hN2 hN1

theorem ballStab_one_γ₁ (hG : G₀ = G₁ ⊔ G₂) :
    ballStab 1 (γ₁ G₀ G₁ G₂) = coreIn (G₁ ⊓ G₂) G₂ ∧
      IsGreatest {N : Subgroup G | N ≤ G₁ ⊓ G₂ ∧ G₂ ≤ Subgroup.normalizer (N : Set G)}
        (ballStab 1 (γ₁ G₀ G₁ G₂)) := by
  have h₁ : G₁ ≤ G₀ := hG ▸ le_sup_left
  have h₂ : G₂ ≤ G₀ := hG ▸ le_sup_right
  have key : ballStab 1 (γ₁ G₀ G₁ G₂) = coreIn (G₁ ⊓ G₂) G₂ := by
    rw [ballStab_one_eq_coreIn hG (adj_γ₀_γ₁ (G₀ := G₀) (G₁ := G₁) (G₂ := G₂)).symm, stab_γ₀ h₁,
      stab_γ₁ h₂, inf_comm]
  refine ⟨key, ?_, ?_⟩
  · rw [key]; exact ⟨coreIn_le_right _ _, le_normalizer_coreIn _ _⟩
  · rintro N ⟨hN1, hN2⟩
    rw [key]
    exact le_coreIn (hN1.trans inf_le_right) hN2 hN1

section Finite

variable [Finite G]

theorem exists_ballStab_eq_bot {T : Subgroup G} (hyp : AmalgamHyp G₀ G₁ G₂ T) :
    ∃ n : ℕ, 0 < n ∧ ∀ γ : CosetGeom G₀ G₁ G₂, ballStab n γ = ⊥ := by
  have hG := hyp.gen
  have h₁ := hyp.le₁
  have h₂ := hyp.le₂
  have hadj : (graph G₀ G₁ G₂).Adj (γ₀ G₀ G₁ G₂) (γ₁ G₀ G₁ G₂) := adj_γ₀_γ₁
  obtain ⟨n₀, hn₀⟩ := WellFoundedLT.antitone_chain_condition (ballStab_antitone (γ₀ G₀ G₁ G₂))
  obtain ⟨n₁, hn₁⟩ := WellFoundedLT.antitone_chain_condition (ballStab_antitone (γ₁ G₀ G₁ G₂))
  have e0 : ∀ m, n₀ ≤ m → ballStab n₀ (γ₀ G₀ G₁ G₂) = ballStab m (γ₀ G₀ G₁ G₂) := hn₀
  have e1 : ∀ m, n₁ ≤ m → ballStab n₁ (γ₁ G₀ G₁ G₂) = ballStab m (γ₁ G₀ G₁ G₂) := hn₁
  set n := max n₀ n₁ + 1 with hn
  have hs0 : ballStab (n + 1) (γ₀ G₀ G₁ G₂) = ballStab n (γ₀ G₀ G₁ G₂) :=
    (e0 (n + 1) (by omega)).symm.trans (e0 n (by omega))
  have hs1 : ballStab (n + 1) (γ₁ G₀ G₁ G₂) = ballStab n (γ₁ G₀ G₁ G₂) :=
    (e1 (n + 1) (by omega)).symm.trans (e1 n (by omega))
  have hK : ballStab n (γ₀ G₀ G₁ G₂) = ballStab n (γ₁ G₀ G₁ G₂) := by
    refine le_antisymm ?_ ?_
    · calc ballStab n (γ₀ G₀ G₁ G₂) = ballStab (n + 1) (γ₀ G₀ G₁ G₂) := hs0.symm
        _ ≤ ballStab n (γ₁ G₀ G₁ G₂) := ballStab_succ_le_of_adj hadj n
    · calc ballStab n (γ₁ G₀ G₁ G₂) = ballStab (n + 1) (γ₁ G₀ G₁ G₂) := hs1.symm
        _ ≤ ballStab n (γ₀ G₀ G₁ G₂) := ballStab_succ_le_of_adj hadj.symm n
  set K := ballStab n (γ₀ G₀ G₁ G₂) with hKdef
  have hKG₁ : K ≤ G₁ := by
    have := ballStab_le_stab n (γ₀ G₀ G₁ G₂)
    rwa [stab_γ₀ h₁] at this
  have hN1 : G₁ ≤ Subgroup.normalizer (K : Set G) := by
    have := le_normalizer_ballStab n (γ₀ G₀ G₁ G₂)
    rwa [stab_γ₀ h₁] at this
  have hN2 : G₂ ≤ Subgroup.normalizer (K : Set G) := by
    have := le_normalizer_ballStab n (γ₁ G₀ G₁ G₂)
    rw [stab_γ₁ h₂, ← hK] at this
    exact this
  have hN0 : G₀ ≤ Subgroup.normalizer (K : Set G) := by
    rw [hG]; exact sup_le hN1 hN2
  have hKbot : K = ⊥ := by
    have hR : pCoreOf 2 K ≤ ⊥ := by
      rw [← hyp.o2_trivial]
      exact pCoreOf_mono_of_le_normalizer (hKG₁.trans h₁) hN0
    have hinf : K ⊓ pCoreOf 2 G₁ ≤ ⊥ := by
      refine le_trans ?_ hR
      rw [inf_comm]
      exact pCoreOf_inf_le hKG₁
    have hcomm : ⁅K, pCoreOf 2 G₁⁆ = ⊥ := by
      refine le_bot_iff.mp (le_trans (commutator_le_inf_of_normalizes ?_ ?_) hinf)
      · exact hKG₁.trans (le_normalizer_pCoreOf 2 G₁)
      · exact (pCoreOf_le 2 G₁).trans hN1
    have hcent : K ≤ Subgroup.centralizer (pCoreOf 2 G₁ : Set G) :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm
    have hle : K ≤ pCoreOf 2 G₁ := fun x hx => hyp.charTwo ⟨hKG₁ hx, hcent hx⟩
    exact le_bot_iff.mp (le_trans (le_inf le_rfl hle) hinf)
  refine ⟨n, by omega, fun γ => ?_⟩
  cases hv : vtype γ with
  | false =>
    obtain ⟨g, hg⟩ := exists_smul_eq_γ₀ hv
    rw [hg, ballStab_smul, ← hKdef, hKbot, conjSub_bot]
  | true =>
    obtain ⟨g, hg⟩ := exists_smul_eq_γ₁ hv
    rw [hg, ballStab_smul, ← hK, hKbot, conjSub_bot]

end Finite

end CosetGeom

end CFSG.Quasithin
