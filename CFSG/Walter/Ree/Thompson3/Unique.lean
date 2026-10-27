module

public import CFSG.Walter.Ree.Thompson3.Compare

public section

namespace CFSG.Walter.Ree.T2.RType

variable {k : Type} [Field k] [CharP k 3] [Finite k] {σ : k ≃+* k} {d : k}

section LJK

variable {G : Type} [Group G] [Finite G] {R : RType G k σ d} {S : k → k × k × k}

@[expose] def lJK (σ : k ≃+* k) (d : k) (S : k → k × k × k) : Set (Option (k × k × k)) :=
  insert (some (1, 1, d)) (Set.range fun x => some (coords (qJK σ d S x)))

theorem S_injective
    (hS : IsS R S) : Function.Injective S := by
  intro x x' h
  have h1 := act_0x1_K hS x
  have h2 := act_0x1_K hS x'
  rw [h, ← h2] at h1
  have := R.act_injective R.K h1
  simpa using this

theorem S_ne_zero
    (hS : IsS R S) (x : k) : S x ≠ (0, 0, 0) := by
  intro h
  have h1 := act_0x1_K hS x
  rw [h, ← R.act_none_K] at h1
  exact Option.some_ne_none _ (R.act_injective R.K h1)

omit [CharP k 3] [Finite k] in
theorem ppv_injective : Function.Injective (ppv σ) := by
  intro v w h
  have := congrArg coords h
  simpa [coords_ppv] using this

theorem qJK_injective
    (hS : IsS R S) : Function.Injective fun x => coords (qJK σ d S x) := by
  intro x x' h
  simp only at h
  have h1 : qJK σ d S x = qJK σ d S x' := by
    rw [← ppv_coords (qJK_mem_P S x), h, ppv_coords (qJK_mem_P S x')]
  simp only [qJK, mul_left_inj] at h1
  have h2 : ppv σ (S (-x)) = ppv σ (S (-x')) := by
    have := congrArg (fun z => ThompsonN.J σ * z * (ThompsonN.J σ)⁻¹) h1
    simpa [mul_assoc] using this
  have := S_injective hS (ppv_injective h2)
  simpa using this

theorem qJK_ne
    (hS : IsS R S) (x : k) : coords (qJK σ d S x) ≠ (1, 1, d) := by
  intro h
  have h1 : qJK σ d S x = pp σ 1 1 d := by
    rw [← ppv_coords (qJK_mem_P S x), h]
  simp only [qJK, mul_eq_right] at h1
  have h2 : ppv σ (S (-x)) = 1 := by
    have := congrArg (fun z => ThompsonN.J σ * z * (ThompsonN.J σ)⁻¹) h1
    simpa [mul_assoc] using this
  exact S_ne_zero hS (-x) (ppv_injective (h2.trans (ppv_zero σ).symm))

theorem ncard_lJK
    (hS : IsS R S) : (lJK σ d S).ncard = Nat.card k + 1 := by
  rw [lJK, Set.ncard_insert_of_notMem]
  · rw [Set.ncard_range_of_injective]
    intro x x' h
    exact qJK_injective hS (Option.some_injective _ h)
  · rintro ⟨x, hx⟩
    exact qJK_ne hS x (Option.some_injective _ hx)

theorem fixSet_JK_eq_lJK
    (hS : IsS R S) : R.fixSet (R.Jg * R.K) = lJK σ d S := by
  symm
  refine Set.eq_of_subset_of_ncard_le ?_ ?_ (Set.toFinite _)
  · rintro ω (rfl | ⟨x, rfl⟩)
    · exact R.JK_fixes_b
    · exact JK_fixes_qJK hS x
  · rw [R.ncard_fixSet_JK, ncard_lJK hS]

end LJK

@[expose] def lines
    {G : Type} [Group G] [Finite G] (R : RType G k σ d) :
    Set (Set (Option (k × k × k))) :=
  {X | ∃ x : G, x * x = 1 ∧ x ≠ 1 ∧ X = R.fixSet x}

variable {G₁ G₂ : Type} [Group G₁] [Finite G₁] [Group G₂] [Finite G₂]
variable (R₁ : RType G₁ k σ d) (R₂ : RType G₂ k σ d)
variable {S : k → k × k × k} (hS₁ : IsS R₁ S) (hS₂ : IsS R₂ S)
variable {a : ℕ} (ha : Even a) (haσ : ∀ x : k, (σ x * x) ^ a = x ^ 2) (h69₁ : Eq69 R₁)
  (h69₂ : Eq69 R₂)

theorem Jg_ne_one'
    {G : Type} [Group G] [Finite G] (R : RType G k σ d) : R.Jg ≠ 1 :=
  fun h1 => by
    have := congrArg (fun z => R.act (some (1, 0, 0)) z) h1
    simp only [act_J, act_one, Option.some.injEq, Prod.mk.injEq] at this
    exact two_ne_zero' (by linear_combination -this.1)

theorem conj_invol {G : Type} [Group G] {x c : G} (hx : x * x = 1) (hx1 : x ≠ 1) :
    c⁻¹ * x * c * (c⁻¹ * x * c) = 1 ∧ c⁻¹ * x * c ≠ 1 := by
  refine ⟨?_, ?_⟩
  · calc c⁻¹ * x * c * (c⁻¹ * x * c) = c⁻¹ * (x * x) * c := by group
      _ = 1 := by rw [hx]; group
  · intro h; apply hx1
    calc x = c * (c⁻¹ * x * c) * c⁻¹ := by group
      _ = 1 := by rw [h]; group

include hS₁ hS₂ ha haσ h69₁ h69₂ in
theorem lines_subset :
    lines R₁ ⊆ lines R₂ := by
  rintro X ⟨x, hx, hx1, rfl⟩
  have himg : ∀ c : ThompsonN k σ, (fun ω => R₁.act ω (R₁.ι c)) =
      fun ω => R₂.act ω (R₂.ι c) := fun c => funext fun ω => act_ι_eq R₁ R₂ ω c
  obtain ⟨c, h | h | h⟩ := R₁.invol_classify hx hx1
  · refine ⟨(R₂.ι c)⁻¹ * R₂.Jg * R₂.ι c, (conj_invol R₂.Jg_mul_Jg R₂.Jg_ne_one').1,
      (conj_invol R₂.Jg_mul_Jg R₂.Jg_ne_one').2, ?_⟩
    rw [h, fixSet_conj, fixSet_conj, himg, fixSet_J_eq R₁ R₂]
  · refine ⟨(R₂.ι c)⁻¹ * R₂.K * R₂.ι c, (conj_invol R₂.K_mul_K R₂.K_ne_one).1,
      (conj_invol R₂.K_mul_K R₂.K_ne_one).2, ?_⟩
    rw [h, fixSet_conj, fixSet_conj, himg, fixSet_K_eq R₁ R₂ hS₁ hS₂ ha haσ h69₁ h69₂]
  · refine ⟨(R₂.ι c)⁻¹ * (R₂.Jg * R₂.K) * R₂.ι c, (conj_invol R₂.JK_mul_JK R₂.JK_ne_one).1,
      (conj_invol R₂.JK_mul_JK R₂.JK_ne_one).2, ?_⟩
    rw [h, fixSet_conj, fixSet_conj, himg, fixSet_JK_eq_lJK hS₁, fixSet_JK_eq_lJK hS₂]

include hS₁ hS₂ ha haσ h69₁ h69₂ in
theorem lines_eq : lines R₁ = lines R₂ :=
  le_antisymm (lines_subset R₁ R₂ hS₁ hS₂ ha haσ h69₁ h69₂)
    (lines_subset R₂ R₁ hS₂ hS₁ ha haσ h69₂ h69₁)

include ha haσ h69₁ in
theorem disjoint_fixSet_J_delta :
    Disjoint (R₁.fixSet R₁.Jg) (R₁.delta ha haσ h69₁) := by
  rw [Set.disjoint_left]
  intro ν hνF hνD
  exact R₁.not_fix_J_of_mem_hOrbit ha haσ h69₁ R₁.act_001_J hνD hνF

include ha haσ h69₁ in
theorem card_U :
    Nat.card k ^ 3 + Nat.card k + 2 ≤
    2 * (R₁.fixSet R₁.Jg ∪ R₁.delta ha haσ h69₁).ncard := by
  rw [Set.ncard_union_eq (R₁.disjoint_fixSet_J_delta ha haσ h69₁) (Set.toFinite _)
    (Set.toFinite _), R₁.ncard_fixSet_J]
  have h1 : Nat.card (R₁.hSub ha haσ h69₁) ≤ 2 * (R₁.delta ha haσ h69₁).ncard :=
    R₁.card_hOrbit ha haσ h69₁ R₁.act_001_J
  have h2 := R₁.card_hSub' ha haσ h69₁
  generalize Nat.card (R₁.hSub ha haσ h69₁) = h at h1 h2
  omega

include hS₁ hS₂ ha haσ h69₁ h69₂ in
theorem U_subset_agree :
    R₁.fixSet R₁.Jg ∪ R₁.delta ha haσ h69₁ ⊆ agree R₁ R₂ :=
  Set.union_subset (R₁.fixSet_J_subset_agree R₂ ha haσ h69₁ h69₂)
    (R₁.delta_subset_agree R₂ hS₁ hS₂ ha haσ h69₁ h69₂)

include R₁ in
theorem three_le_card_k :
    3 ≤ Nat.card k := by
  rw [R₁.card_k]; exact R₁.hyp.three_le_q

@[expose] noncomputable def inv2
    {G : Type} [Group G] [Finite G] (R : RType G k σ d)
    (ω u : Option (k × k × k)) : G := by
  classical
  exact if h : ω ≠ u then Classical.choose (R.exists_invol_fixes_two h) else 1

theorem inv2_spec
    {G : Type} [Group G] [Finite G] (R : RType G k σ d)
    {ω u : Option (k × k × k)} (h : ω ≠ u) :
    R.inv2 ω u * R.inv2 ω u = 1 ∧ R.inv2 ω u ≠ 1 ∧ R.act ω (R.inv2 ω u) = ω ∧
      R.act u (R.inv2 ω u) = u := by
  classical
  simp only [inv2, h, ne_eq, not_false_eq_true, dite_true]
  exact Classical.choose_spec (R.exists_invol_fixes_two h)

theorem image_fixSet_K
    {G : Type} [Group G] [Finite G] (R : RType G k σ d) (x : G) :
    (fun ω => R.act ω R.K) '' R.fixSet x = R.fixSet (R.K⁻¹ * x * R.K) :=
  (R.fixSet_conj x R.K).symm

include hS₁ hS₂ ha haσ h69₁ h69₂ in
theorem image_line_eq
    {x : G₁} (hx : x * x = 1) (hx1 : x ≠ 1) {u₁ u₂ : Option (k × k × k)}
    (hu : u₁ ≠ u₂) (hu₁ : u₁ ∈ R₁.fixSet x) (hu₂ : u₂ ∈ R₁.fixSet x)
    (hA₁ : u₁ ∈ agree R₁ R₂) (hA₂ : u₂ ∈ agree R₁ R₂) :
    (fun ω => R₁.act ω R₁.K) '' R₁.fixSet x = (fun ω => R₂.act ω R₂.K) '' R₁.fixSet x := by
  have hL := lines_eq R₁ R₂ hS₁ hS₂ ha haσ h69₁ h69₂
  obtain ⟨y, hy, hy1, hly⟩ : R₁.fixSet x ∈ lines R₂ := hL ▸ ⟨x, hx, hx1, rfl⟩
  have hK1 : R₁.fixSet (R₁.K⁻¹ * x * R₁.K) ∈ lines R₁ :=
    ⟨_, (conj_invol hx hx1).1, (conj_invol hx hx1).2, rfl⟩
  obtain ⟨z, hz, hz1, hlz⟩ : R₁.fixSet (R₁.K⁻¹ * x * R₁.K) ∈ lines R₂ := hL ▸ hK1
  rw [image_fixSet_K, hlz, hly, image_fixSet_K]
  have hκ : ∀ u ∈ R₁.fixSet x, u ∈ agree R₁ R₂ →
      R₁.act u R₁.K ∈ R₂.fixSet z ∧ R₁.act u R₁.K ∈ R₂.fixSet (R₂.K⁻¹ * y * R₂.K) := by
    intro u hu hA
    refine ⟨?_, ?_⟩
    · rw [← hlz, ← image_fixSet_K]; exact ⟨u, hu, rfl⟩
    · rw [show R₁.act u R₁.K = R₂.act u R₂.K from hA, ← image_fixSet_K, ← hly]
      exact ⟨u, hu, rfl⟩
  obtain ⟨a₁, b₁⟩ := hκ u₁ hu₁ hA₁
  obtain ⟨a₂, b₂⟩ := hκ u₂ hu₂ hA₂
  have hne : R₁.act u₁ R₁.K ≠ R₁.act u₂ R₁.K := fun h => hu (R₁.act_injective _ h)
  have := R₂.invol_unique hne hz hz1 a₁ a₂ (conj_invol hy hy1).1 (conj_invol hy hy1).2 b₁ b₂
  rw [this]

include hS₁ hS₂ ha haσ h69₁ h69₂ in
theorem act_K_eq_of_not_mem
    {ω : Option (k × k × k)}
    (hω : ω ∉ R₁.fixSet R₁.Jg ∪ R₁.delta ha haσ h69₁) : ω ∈ agree R₁ R₂ := by
  set U := R₁.fixSet R₁.Jg ∪ R₁.delta ha haσ h69₁ with hUdef
  have hUA := U_subset_agree R₁ R₂ hS₁ hS₂ ha haσ h69₁ h69₂
  have hcardU := R₁.card_U ha haσ h69₁
  have hq3 := R₁.three_le_card_k
  have hT := R₁.ncard_invSet_le ω
  have hU : Nat.card k ^ 2 + Nat.card k + 2 ≤ U.ncard := by
    rw [← hUdef] at hcardU
    generalize U.ncard = u at hcardU
    generalize hq : Nat.card k = q at hcardU hq3
    nlinarith
  have hne : ∀ u ∈ U, ω ≠ u := fun u hu h => hω (h ▸ hu)
  set φ : Option (k × k × k) → G₁ := fun u => R₁.inv2 ω u
  have hφ : ∀ u ∈ U, φ u ∈ R₁.invSet ω := fun u hu =>
    ⟨(R₁.inv2_spec (hne u hu)).1, (R₁.inv2_spec (hne u hu)).2.1, (R₁.inv2_spec (hne u hu)).2.2.1⟩
  have hφu : ∀ u ∈ U, u ∈ R₁.fixSet (φ u) := fun u hu => (R₁.inv2_spec (hne u hu)).2.2.2
  obtain ⟨u₁, hu₁, u₂, hu₂, h12, hφ12⟩ := Set.exists_ne_map_eq_of_ncard_lt_of_maps_to
    (s := U) (t := R₁.invSet ω) (by omega) hφ (Set.toFinite _)
  have hx₁ := hφ u₁ hu₁
  have hU' : U.ncard - (R₁.fixSet (φ u₁)).ncard ≤ (U \ R₁.fixSet (φ u₁)).ncard :=
    Set.le_ncard_sdiff _ _ (Set.toFinite _)
  rw [R₁.ncard_fixSet_invol hx₁.1 hx₁.2.1] at hU'
  have hT' : (R₁.invSet ω \ {(φ u₁)}).ncard ≤ Nat.card k ^ 2 :=
    (Set.ncard_le_ncard Set.sdiff_subset (Set.toFinite _)).trans hT
  obtain ⟨u₃, hu₃, u₄, hu₄, h34, hφ34⟩ := Set.exists_ne_map_eq_of_ncard_lt_of_maps_to
    (s := U \ R₁.fixSet (φ u₁)) (t := R₁.invSet ω \ {(φ u₁)}) (f := φ) (by omega) (by
      rintro u ⟨huU, hux⟩
      refine ⟨hφ u huU, fun h => hux ?_⟩
      rw [Set.mem_singleton_iff] at h
      rw [← h]; exact hφu u huU) (Set.toFinite _)
  have hx₂ := hφ u₃ hu₃.1
  have hx12 : (φ u₁) ≠ (φ u₃) := by
    intro h
    exact hu₃.2 (h ▸ hφu u₃ hu₃.1)
  have hl₁ := image_line_eq R₁ R₂ hS₁ hS₂ ha haσ h69₁ h69₂ hx₁.1 hx₁.2.1 h12 (hφu u₁ hu₁)
    (hφ12 ▸ hφu u₂ hu₂) (hUA hu₁) (hUA hu₂)
  have hl₂ := image_line_eq R₁ R₂ hS₁ hS₂ ha haσ h69₁ h69₂ hx₂.1 hx₂.2.1 h34 (hφu u₃ hu₃.1)
    (hφ34 ▸ hφu u₄ hu₄.1) (hUA hu₃.1) (hUA hu₄.1)
  have hinter : R₁.fixSet (φ u₁) ∩ R₁.fixSet (φ u₃) = {ω} := by
    ext μ
    simp only [Set.mem_inter_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨h1, h2⟩
      by_contra hμ
      exact hx12 (R₁.invol_unique (Ne.symm hμ) hx₁.1 hx₁.2.1 hx₁.2.2 h1 hx₂.1 hx₂.2.1 hx₂.2.2 h2)
    · rintro rfl; exact ⟨hx₁.2.2, hx₂.2.2⟩
  have h1 : R₁.act ω R₁.K ∈ (fun ω => R₁.act ω R₁.K) '' (R₁.fixSet (φ u₁) ∩ R₁.fixSet (φ u₃)) := by
    rw [hinter]; exact ⟨ω, rfl, rfl⟩
  rw [Set.image_inter (R₁.act_injective _), hl₁, hl₂, ← Set.image_inter (R₂.act_injective _),
    hinter, Set.image_singleton] at h1
  exact h1

include hS₁ hS₂ ha haσ h69₁ h69₂ in
theorem act_K_eq
    (ω : Option (k × k × k)) : R₁.act ω R₁.K = R₂.act ω R₂.K := by
  by_cases hω : ω ∈ R₁.fixSet R₁.Jg ∪ R₁.delta ha haσ h69₁
  · exact U_subset_agree R₁ R₂ hS₁ hS₂ ha haσ h69₁ h69₂ hω
  · exact act_K_eq_of_not_mem R₁ R₂ hS₁ hS₂ ha haσ h69₁ h69₂ hω

theorem mem_N_or_pres
    {G : Type} [Group G] [Finite G] (R : RType G k σ d) (g : G) :
    (∃ ν, g = R.ι ν) ∨ ∃ ν v, g = R.ι ν * R.K * R.ι (ppv σ v) := by
  by_cases hg : g ∈ R.N
  · exact Or.inl (R.exists_ι hg)
  · obtain ⟨v, ν, h⟩ := R.exists_pres' hg
    exact Or.inr ⟨ν, v, h⟩

include hS₁ hS₂ ha haσ h69₁ h69₂ in
theorem ρ_range_le :
    R₁.ρ.range ≤ R₂.ρ.range := by
  have hι : ∀ ν, R₁.ρ (R₁.ι ν) = R₂.ρ (R₂.ι ν) := fun ν => by
    ext ω
    rw [ρ_apply, ρ_apply, ← map_inv, ← map_inv, act_ι_eq R₁ R₂]
  have hK : R₁.ρ R₁.K = R₂.ρ R₂.K := by
    ext ω
    rw [ρ_apply, ρ_apply, R₁.K_inv_eq, R₂.K_inv_eq, act_K_eq R₁ R₂ hS₁ hS₂ ha haσ h69₁ h69₂]
  rintro _ ⟨g, rfl⟩
  rcases mem_N_or_pres R₁ g with ⟨ν, rfl⟩ | ⟨ν, v, rfl⟩
  · exact ⟨R₂.ι ν, (hι ν).symm⟩
  · exact ⟨R₂.ι ν * R₂.K * R₂.ι (ppv σ v), by simp only [map_mul, hι, hK]⟩

include hS₁ hS₂ ha haσ h69₁ h69₂ in
theorem nonempty_mulEquiv :
    Nonempty (G₁ ≃* G₂) := by
  have h : R₁.ρ.range = R₂.ρ.range :=
    le_antisymm (ρ_range_le R₁ R₂ hS₁ hS₂ ha haσ h69₁ h69₂)
      (ρ_range_le R₂ R₁ hS₂ hS₁ ha haσ h69₂ h69₁)
  exact ⟨(MonoidHom.ofInjective R₁.ρ_injective).trans ((MulEquiv.subgroupCongr h).trans
    (MonoidHom.ofInjective R₂.ρ_injective).symm)⟩

end CFSG.Walter.Ree.T2.RType
