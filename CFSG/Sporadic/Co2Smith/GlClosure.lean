module

public import CFSG.Sporadic.Co2Smith.GlDefs
public import CFSG.Sporadic.Co2Rank3.Recognition

public section

namespace CFSG.Sporadic.Co2Smith

open Subgroup MulAction CFSG.Sporadic.Co2Rank3

section Closure

variable {G : Type*} [Group G] {G₁ : Subgroup G} {u v : G}

theorem one_mem_smithX : (1 : G) ∈ smithX G₁ u v :=
  Or.inl G₁.one_mem

theorem mul_mem_smithX {x g : G} (hx : x ∈ smithX G₁ u v) (hg : g ∈ G₁) :
    x * g ∈ smithX G₁ u v := by
  rcases hx with hx | ⟨a, ha, b, hb, rfl⟩ | ⟨a, ha, b, hb, rfl⟩
  · exact Or.inl (G₁.mul_mem hx hg)
  · exact Or.inr (Or.inl ⟨a, ha, b * g, G₁.mul_mem hb hg, mul_assoc _ _ _⟩)
  · exact Or.inr (Or.inr ⟨a, ha, b * g, G₁.mul_mem hb hg, mul_assoc _ _ _⟩)

theorem mul_inv_mem_smithX [Finite G] {w : G}
    (hw : ∀ x ∈ smithX G₁ u v, x * w ∈ smithX G₁ u v) {x : G} (hx : x ∈ smithX G₁ u v) :
    x * w⁻¹ ∈ smithX G₁ u v := by
  let f : smithX G₁ u v → smithX G₁ u v := fun y => ⟨y * w, hw y y.2⟩
  have hf : Function.Injective f := fun a b hab =>
    Subtype.ext (mul_right_cancel (congrArg Subtype.val hab))
  obtain ⟨y, hy⟩ := Finite.injective_iff_surjective.1 hf ⟨x, hx⟩
  have e : (y : G) * w = x := congrArg Subtype.val hy
  rw [← e, mul_inv_cancel_right]
  exact y.2

theorem mul_mem_smithX_of_mem_closure [Finite G]
    (hX : ∀ x ∈ smithX G₁ u v, x * u ∈ smithX G₁ u v) {g : G}
    (hg : g ∈ closure ((G₁ : Set G) ∪ {u})) {x : G} (hx : x ∈ smithX G₁ u v) :
    x * g ∈ smithX G₁ u v := by
  induction hg using Subgroup.closure_induction generalizing x with
  | mem g hg =>
    rcases hg with hg | hg
    · exact mul_mem_smithX hx hg
    · rw [Set.mem_singleton_iff.1 hg]
      exact hX x hx
  | one => simpa using hx
  | mul g₁ g₂ _ _ ih₁ ih₂ =>
    rw [← mul_assoc]
    exact ih₂ (ih₁ hx)
  | inv g _ ih => exact mul_inv_mem_smithX (fun y hy => ih hy) hx

theorem closure_eq_smithX [Finite G] (hX : ∀ x ∈ smithX G₁ u v, x * u ∈ smithX G₁ u v)
    (hv : v ∈ closure ((G₁ : Set G) ∪ {u})) :
    (closure ((G₁ : Set G) ∪ {u}) : Set G) = smithX G₁ u v := by
  refine Set.Subset.antisymm (fun g hg => ?_) ?_
  · simpa using mul_mem_smithX_of_mem_closure hX hg one_mem_smithX
  · have hG₁ : ∀ a ∈ G₁, a ∈ closure ((G₁ : Set G) ∪ {u}) := fun a ha =>
      subset_closure (Or.inl ha)
    have hu : u ∈ closure ((G₁ : Set G) ∪ {u}) := subset_closure (Or.inr rfl)
    rintro g (hg | ⟨a, ha, b, hb, rfl⟩ | ⟨a, ha, b, hb, rfl⟩)
    · exact hG₁ g hg
    · exact mul_mem (mul_mem (hG₁ a ha) hu) (hG₁ b hb)
    · exact mul_mem (mul_mem (hG₁ a ha) hv) (hG₁ b hb)

end Closure

section Count

variable {G : Type*} [Group G] {G₁ : Subgroup G}

theorem smithX_inv (u v : G) : (smithX G₁ u v)⁻¹ = smithX G₁ u⁻¹ v⁻¹ := by
  have key : ∀ w g : G, (∃ a ∈ G₁, ∃ b ∈ G₁, g⁻¹ = a * w * b) ↔
      ∃ a ∈ G₁, ∃ b ∈ G₁, g = a * w⁻¹ * b := by
    intro w g
    constructor
    · rintro ⟨a, ha, b, hb, e⟩
      refine ⟨b⁻¹, G₁.inv_mem hb, a⁻¹, G₁.inv_mem ha, ?_⟩
      rw [← inv_inv g, e]
      group
    · rintro ⟨a, ha, b, hb, rfl⟩
      exact ⟨b⁻¹, G₁.inv_mem hb, a⁻¹, G₁.inv_mem ha, by group⟩
  ext g
  simp only [Set.mem_inv, smithX, Set.mem_ofPred_eq]
  exact or_congr (inv_mem_iff) (or_congr (key u g) (key v g))

theorem mk_mem_orbit_iff {w g : G} :
    (g : G ⧸ G₁) ∈ orbit G₁ (w : G ⧸ G₁) ↔ ∃ a ∈ G₁, ∃ b ∈ G₁, g = a * w * b := by
  rw [mem_orbit_iff]
  constructor
  · rintro ⟨a, ha⟩
    rw [Subgroup.smul_def, MulAction.Quotient.smul_coe, smul_eq_mul, QuotientGroup.eq] at ha
    exact ⟨a, a.2, (a * w)⁻¹ * g, ha, by group⟩
  · rintro ⟨a, ha, b, hb, rfl⟩
    refine ⟨⟨a, ha⟩, ?_⟩
    rw [Subgroup.smul_def, MulAction.Quotient.smul_coe, smul_eq_mul, QuotientGroup.eq]
    simpa [mul_assoc] using hb

theorem smithX_eq_preimage (w₁ w₂ : G) :
    smithX G₁ w₁ w₂ = QuotientGroup.mk ⁻¹' (orbit G₁ ((1 : G) : G ⧸ G₁) ∪
      orbit G₁ (w₁ : G ⧸ G₁) ∪ orbit G₁ (w₂ : G ⧸ G₁)) := by
  have h1 : ∀ g : G, (∃ a ∈ G₁, ∃ b ∈ G₁, g = a * 1 * b) ↔ g ∈ G₁ := by
    intro g
    constructor
    · rintro ⟨a, ha, b, hb, rfl⟩
      simpa using G₁.mul_mem ha hb
    · exact fun hg => ⟨g, hg, 1, G₁.one_mem, by simp⟩
  ext g
  simp only [Set.mem_preimage, Set.mem_union, mk_mem_orbit_iff, h1, or_assoc]
  rfl

theorem ncard_orbit_one_mk : (orbit G₁ ((1 : G) : G ⧸ G₁)).ncard = 1 := by
  rw [← index_stabilizer]
  convert Subgroup.index_top
  refine eq_top_iff.2 fun k _ => mem_stabilizer_iff.2 ?_
  rw [Subgroup.smul_def, MulAction.Quotient.smul_coe, smul_eq_mul, mul_one, QuotientGroup.eq,
    mul_one]
  exact G₁.inv_mem k.2

theorem natCard_smithX_of_ncard [Finite G] {w₁ w₂ : G} {n₁ n₂ : ℕ}
    (h₁ : (orbit G₁ (w₁ : G ⧸ G₁)).ncard = n₁) (h₂ : (orbit G₁ (w₂ : G ⧸ G₁)).ncard = n₂)
    (hn₁ : n₁ ≠ 1) (hn₂ : n₂ ≠ 1) (hn : n₁ ≠ n₂) :
    Nat.card (smithX G₁ w₁ w₂) = Nat.card G₁ * (1 + n₁ + n₂) := by
  have hd : ∀ {x y : G ⧸ G₁}, (orbit G₁ x).ncard ≠ (orbit G₁ y).ncard →
      Disjoint (orbit G₁ x) (orbit G₁ y) := fun h =>
    (orbit.eq_or_disjoint _ _).resolve_left fun e => h (by rw [e])
  have h0 := ncard_orbit_one_mk (G₁ := G₁)
  rw [smithX_eq_preimage, QuotientGroup.card_preimage_mk, Nat.card_coe_set_eq,
    Set.ncard_union_eq (Set.disjoint_union_left.2 ⟨hd (by rw [h0, h₂]; exact hn₂.symm),
      hd (by rw [h₁, h₂]; exact hn)⟩),
    Set.ncard_union_eq (hd (by rw [h0, h₁]; exact hn₁.symm)), h0, h₁, h₂]

theorem smul_inv_mk_eq_iff {w : G} (k : G₁) :
    k • ((w⁻¹ : G) : G ⧸ G₁) = ((w⁻¹ : G) : G ⧸ G₁) ↔ w * k * w⁻¹ ∈ G₁ := by
  rw [Subgroup.smul_def, MulAction.Quotient.smul_coe, smul_eq_mul, QuotientGroup.eq,
    show ((k : G) * w⁻¹)⁻¹ * w⁻¹ = (w * k * w⁻¹)⁻¹ by group, inv_mem_iff]

theorem ncard_orbit_inv_mk (ψ : G₁ ≃* co2P0) {w : G} {x : Fin 2300}
    (hw : ∀ h : G₁, w * h * w⁻¹ ∈ G₁ ↔ (ψ h : Equiv.Perm (Fin 2300)) x = x) :
    (orbit G₁ ((w⁻¹ : G) : G ⧸ G₁)).ncard = (orbit co2P0 x).ncard := by
  rw [← index_stabilizer, ← index_stabilizer]
  have e : stabilizer G₁ ((w⁻¹ : G) : G ⧸ G₁) = (stabilizer co2P0 x).comap ψ.toMonoidHom := by
    ext k
    rw [mem_stabilizer_iff, smul_inv_mk_eq_iff, hw, Subgroup.mem_comap, mem_stabilizer_iff]
    rfl
  rw [e, Subgroup.index_comap_of_surjective _ ψ.surjective]

theorem natCard_smithX
    [Finite G] {u v : G} (ψ : G₁ ≃* co2P0)
    (hu : ∀ h : G₁, (ψ h : Equiv.Perm (Fin 2300)) 3 = 3 → u * h * u⁻¹ ∈ G₁)
    (hun : u ∉ normalizer (G₁ : Set G))
    (hv : ∀ h : G₁, (ψ h : Equiv.Perm (Fin 2300)) 1 = 1 → v * h * v⁻¹ ∈ G₁)
    (hvn : v ∉ normalizer (G₁ : Set G)) :
    Nat.card (smithX G₁ u v) = 2300 * Nat.card G₁ := by
  have hu' := stab_iff_of_maximal ψ (fun _ h1 h2 => co2P03_maximal h1 h2) hu
    (exists_not_mem_of_not_mem_normalizer hun)
  have hv' := stab_iff_of_maximal ψ (fun _ h1 h2 => co2P01_maximal h1 h2) hv
    (exists_not_mem_of_not_mem_normalizer hvn)
  have e : smithX G₁ u v = (smithX G₁ u⁻¹ v⁻¹)⁻¹ := by rw [smithX_inv, inv_inv, inv_inv]
  rw [e, Set.natCard_inv, natCard_smithX_of_ncard ((ncard_orbit_inv_mk ψ hu').trans
    ncard_co2Delta) ((ncard_orbit_inv_mk ψ hv').trans ncard_co2Gamma) (by norm_num)
    (by norm_num) (by norm_num)]
  ring

theorem natCard_smithX_eq
    [Finite G] {u v : G} (ψ : G₁ ≃* co2P0)
    (hu : ∀ h : G₁, (ψ h : Equiv.Perm (Fin 2300)) 3 = 3 → u * h * u⁻¹ ∈ G₁)
    (hun : u ∉ normalizer (G₁ : Set G))
    (hv : ∀ h : G₁, (ψ h : Equiv.Perm (Fin 2300)) 1 = 1 → v * h * v⁻¹ ∈ G₁)
    (hvn : v ∉ normalizer (G₁ : Set G)) :
    Nat.card (smithX G₁ u v) = 42305421312000 := by
  rw [natCard_smithX ψ hu hun hv hvn, Nat.card_congr ψ.toEquiv, card_co2P0]

theorem natCard_closure_eq
    [Finite G] {u v : G} (ψ : G₁ ≃* co2P0)
    (hu : ∀ h : G₁, (ψ h : Equiv.Perm (Fin 2300)) 3 = 3 → u * h * u⁻¹ ∈ G₁)
    (hun : u ∉ normalizer (G₁ : Set G))
    (hv : ∀ h : G₁, (ψ h : Equiv.Perm (Fin 2300)) 1 = 1 → v * h * v⁻¹ ∈ G₁)
    (hvn : v ∉ normalizer (G₁ : Set G)) (hX : ∀ x ∈ smithX G₁ u v, x * u ∈ smithX G₁ u v)
    (hvc : v ∈ closure ((G₁ : Set G) ∪ {u})) :
    Nat.card (closure ((G₁ : Set G) ∪ {u})) = 42305421312000 := by
  rw [← natCard_smithX_eq ψ hu hun hv hvn, ← closure_eq_smithX hX hvc]
  rfl

end Count

end CFSG.Sporadic.Co2Smith
