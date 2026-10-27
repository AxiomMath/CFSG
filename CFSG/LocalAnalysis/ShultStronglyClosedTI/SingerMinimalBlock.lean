module

public import CFSG.LocalAnalysis.ShultStronglyClosedTI.SingerScalar
public import Mathlib.LinearAlgebra.Projectivization.Cardinality

public noncomputable section

namespace CFSG.ShultStronglyClosedTI.Singer

open scoped LinearAlgebra.Projectivization Pointwise
open Projectivization Module

variable (k F : Type*) [Field k] [Field F] [Algebra k F]

structure MinimalBlock where
  G : Subgroup (F ≃ₗ[k] F)
  scalars_le : scalars k F ≤ G
  Δ : Set (ℙ k F)
  isBlock : ∀ g ∈ G, g • Δ = Δ ∨ Disjoint (g • Δ) Δ
  one_lt_ncard : 1 < Δ.ncard
  ne_univ : Δ ≠ Set.univ
  minimal : ∀ X : Set (ℙ k F), (∀ g ∈ G, g • X = X ∨ Disjoint (g • X) X) → 1 < X.ncard →
    Δ.ncard ≤ X.ncard

namespace MinimalBlock

variable {k F} (M : MinimalBlock k F)

theorem units_mem (c : Fˣ) : scalarHom k F c ∈ M.G :=
  M.scalars_le (scalarHom_mem_scalars c)

theorem nonempty : M.Δ.Nonempty :=
  Set.nonempty_of_ncard_ne_zero (by have := M.one_lt_ncard; omega)

theorem smul_eq_smul_of_mem {g₁ g₂ : F ≃ₗ[k] F} (h₁ : g₁ ∈ M.G) (h₂ : g₂ ∈ M.G) {p : ℙ k F}
    (hp₁ : p ∈ g₁ • M.Δ) (hp₂ : p ∈ g₂ • M.Δ) : g₁ • M.Δ = g₂ • M.Δ := by
  obtain ⟨a, ha, rfl⟩ := hp₁
  obtain ⟨b, hb, hab⟩ := hp₂
  simp only at hab
  have hmem : (g₂⁻¹ * g₁) • a ∈ M.Δ := by
    rw [mul_smul, ← hab, inv_smul_smul]
    exact hb
  rcases M.isBlock _ (M.G.mul_mem (M.G.inv_mem h₂) h₁) with h | h
  · rw [mul_smul, inv_smul_eq_iff] at h
    exact h
  · exact absurd hmem (Set.disjoint_left.mp h (Set.smul_mem_smul_set ha))

@[expose] def blocks : Set (Set (ℙ k F)) := {Γ | ∃ g ∈ M.G, g • M.Δ = Γ}

theorem Δ_mem_blocks : M.Δ ∈ M.blocks := ⟨1, M.G.one_mem, one_smul _ _⟩

theorem smul_mem_blocks {g : F ≃ₗ[k] F} (hg : g ∈ M.G) {Γ : Set (ℙ k F)} (hΓ : Γ ∈ M.blocks) :
    g • Γ ∈ M.blocks := by
  obtain ⟨g', hg', rfl⟩ := hΓ
  exact ⟨g * g', M.G.mul_mem hg hg', mul_smul _ _ _⟩

theorem eq_of_mem_blocks {Γ Γ' : Set (ℙ k F)} (hΓ : Γ ∈ M.blocks) (hΓ' : Γ' ∈ M.blocks)
    {p : ℙ k F} (hp : p ∈ Γ) (hp' : p ∈ Γ') : Γ = Γ' := by
  obtain ⟨g, hg, rfl⟩ := hΓ
  obtain ⟨g', hg', rfl⟩ := hΓ'
  exact M.smul_eq_smul_of_mem hg hg' hp hp'

theorem smul_eq_of_mem {Γ : Set (ℙ k F)} (hΓ : Γ ∈ M.blocks) {g : F ≃ₗ[k] F} (hg : g ∈ M.G)
    {p : ℙ k F} (hp : p ∈ Γ) (hgp : g • p ∈ Γ) : g • Γ = Γ :=
  M.eq_of_mem_blocks (M.smul_mem_blocks hg hΓ) hΓ (Set.smul_mem_smul_set hp) hgp

theorem units_smul_mem_blocks (c : Fˣ) : c • M.Δ ∈ M.blocks :=
  ⟨scalarHom k F c, M.units_mem c, scalarHom_smul_set c M.Δ⟩

theorem exists_units_mem (p : ℙ k F) : ∃ c : Fˣ, p ∈ c • M.Δ := by
  obtain ⟨q, hq⟩ := M.nonempty
  obtain ⟨c, hc⟩ := exists_units_smul_eq q p
  exact ⟨c, hc ▸ Set.smul_mem_smul_set hq⟩

theorem exists_mem_blocks (p : ℙ k F) : ∃ Γ ∈ M.blocks, p ∈ Γ := by
  obtain ⟨c, hc⟩ := M.exists_units_mem p
  exact ⟨_, M.units_smul_mem_blocks c, hc⟩

theorem exists_units_eq {Γ : Set (ℙ k F)} (hΓ : Γ ∈ M.blocks) :
    ∃ c : Fˣ, c • M.Δ = Γ := by
  obtain ⟨g, hg, rfl⟩ := hΓ
  obtain ⟨q, hq⟩ := M.nonempty
  obtain ⟨c, hc⟩ := M.exists_units_mem (g • q)
  exact ⟨c, M.eq_of_mem_blocks (M.units_smul_mem_blocks c) ⟨g, hg, rfl⟩ hc
    (Set.smul_mem_smul_set hq)⟩

@[expose] def K : Subgroup (F ≃ₗ[k] F) where
  carrier := {g | g ∈ M.G ∧ ∀ Γ ∈ M.blocks, g • Γ = Γ}
  mul_mem' := by
    rintro g h ⟨hg, hgΓ⟩ ⟨hh, hhΓ⟩
    exact ⟨M.G.mul_mem hg hh, fun Γ hΓ => by rw [mul_smul, hhΓ Γ hΓ, hgΓ Γ hΓ]⟩
  one_mem' := ⟨M.G.one_mem, fun Γ _ => one_smul _ _⟩
  inv_mem' := by
    rintro g ⟨hg, hgΓ⟩
    exact ⟨M.G.inv_mem hg, fun Γ hΓ => by
      rw [inv_smul_eq_iff]
      exact (hgΓ Γ hΓ).symm⟩

theorem mem_K {g : F ≃ₗ[k] F} : g ∈ M.K ↔ g ∈ M.G ∧ ∀ Γ ∈ M.blocks, g • Γ = Γ :=
  Iff.rfl

theorem K_le : M.K ≤ M.G := fun _ h => h.1

theorem smul_eq_of_mem_K {h : F ≃ₗ[k] F} (hh : h ∈ M.K) {Γ : Set (ℙ k F)}
    (hΓ : Γ ∈ M.blocks) : h • Γ = Γ :=
  hh.2 Γ hΓ

theorem smul_mem_iff_of_mem_K {h : F ≃ₗ[k] F} (hh : h ∈ M.K) {Γ : Set (ℙ k F)}
    (hΓ : Γ ∈ M.blocks) {p : ℙ k F} : h • p ∈ Γ ↔ p ∈ Γ := by
  conv_lhs => rw [← M.smul_eq_of_mem_K hh hΓ]
  exact Set.smul_mem_smul_set_iff

theorem conj_mem_K {g : F ≃ₗ[k] F} (hg : g ∈ M.G) {h : F ≃ₗ[k] F} (hh : h ∈ M.K) :
    g * h * g⁻¹ ∈ M.K := by
  refine ⟨M.G.mul_mem (M.G.mul_mem hg (M.K_le hh)) (M.G.inv_mem hg), fun Γ hΓ => ?_⟩
  rw [mul_smul, mul_smul, M.smul_eq_of_mem_K hh (M.smul_mem_blocks (M.G.inv_mem hg) hΓ),
    smul_inv_smul]

@[expose] def Bu : Subgroup Fˣ := MulAction.stabilizer Fˣ M.Δ

theorem mem_Bu {c : Fˣ} : c ∈ M.Bu ↔ c • M.Δ = M.Δ :=
  MulAction.mem_stabilizer_iff

theorem Bu_smul_eq {c : Fˣ} (hc : c ∈ M.Bu) {Γ : Set (ℙ k F)} (hΓ : Γ ∈ M.blocks) :
    c • Γ = Γ := by
  obtain ⟨c', rfl⟩ := M.exists_units_eq hΓ
  rw [smul_smul, mul_comm, ← smul_smul, M.mem_Bu.mp hc]

theorem Bu_smul_mem_iff {c : Fˣ} (hc : c ∈ M.Bu) {Γ : Set (ℙ k F)}
    (hΓ : Γ ∈ M.blocks) {p : ℙ k F} : c • p ∈ Γ ↔ p ∈ Γ := by
  conv_lhs => rw [← M.Bu_smul_eq hc hΓ]
  exact Set.smul_mem_smul_set_iff

theorem scalarHom_mem_K {c : Fˣ} (hc : c ∈ M.Bu) : scalarHom k F c ∈ M.K :=
  ⟨M.units_mem c, fun Γ hΓ => by rw [scalarHom_smul_set, M.Bu_smul_eq hc hΓ]⟩

theorem Bu_transitive {Γ : Set (ℙ k F)} (hΓ : Γ ∈ M.blocks) {p q : ℙ k F}
    (hp : p ∈ Γ) (hq : q ∈ Γ) : ∃ c ∈ M.Bu, c • p = q := by
  obtain ⟨c, rfl⟩ := exists_units_smul_eq p q
  refine ⟨c, ?_, rfl⟩
  have h1 : c • Γ = Γ := by
    rw [← scalarHom_smul_set]
    exact M.smul_eq_of_mem hΓ (M.units_mem c) hp (by rwa [scalarHom_smul])
  obtain ⟨c', rfl⟩ := M.exists_units_eq hΓ
  rw [smul_smul, mul_comm, ← smul_smul] at h1
  exact M.mem_Bu.mpr (smul_left_cancel c' h1)

theorem Bu_smul_mem_blocks {Γ : Set (ℙ k F)} (hΓ : Γ ∈ M.blocks) {p : ℙ k F}
    (hp : p ∈ Γ) {c : Fˣ} (hc : c ∈ M.Bu) : c • p ∈ Γ :=
  (M.Bu_smul_mem_iff hc hΓ).mpr hp

theorem exists_Bu_notMem [Finite F] :
    ∃ c ∈ M.Bu, (c : F) ∉ Set.range (algebraMap k F) := by
  obtain ⟨x, y, hx, hy, hxy⟩ := (Set.one_lt_ncard_iff (Set.toFinite M.Δ)).mp M.one_lt_ncard
  obtain ⟨c, hc, hcxy⟩ := M.Bu_transitive M.Δ_mem_blocks hx hy
  exact ⟨c, hc, fun h => hxy ((units_smul_eq_self_iff.mpr h).symm.trans hcxy)⟩

@[expose] def l : IntermediateField k F := IntermediateField.adjoin k ((↑) '' (M.Bu : Set Fˣ))

theorem coe_mem_l {c : Fˣ} (hc : c ∈ M.Bu) : (c : F) ∈ M.l :=
  IntermediateField.subset_adjoin k _ ⟨c, hc, rfl⟩

theorem mem_l_iff [Finite F] {a : F} :
    a ∈ M.l ↔ a ∈ Submodule.span k ((↑) '' (M.Bu : Set Fˣ) : Set F) := by
  have : FiniteDimensional k F := Module.Finite.of_finite
  have h := IntermediateField.adjoin_toSubalgebra_of_isAlgebraic (F := k)
    (S := ((↑) '' (M.Bu : Set Fˣ) : Set F)) fun x _ => Algebra.IsAlgebraic.isAlgebraic x
  have hcl : (Submonoid.closure ((↑) '' (M.Bu : Set Fˣ) : Set F) : Set F) =
      (↑) '' (M.Bu : Set Fˣ) := by
    have := Submonoid.closure_eq (M.Bu.toSubmonoid.map (Units.coeHom F))
    rw [Submonoid.coe_map] at this
    exact congrArg SetLike.coe this
  rw [← IntermediateField.mem_toSubalgebra, l, h, ← Subalgebra.mem_toSubmodule,
    Algebra.adjoin_eq_span, hcl]

theorem l_ne_bot [Finite F] : M.l ≠ ⊥ := by
  intro h
  obtain ⟨c, hc, hck⟩ := M.exists_Bu_notMem
  have := M.coe_mem_l hc
  rw [h, IntermediateField.mem_bot] at this
  exact hck this

theorem exists_mem_l_mul [Finite F] {g : F ≃ₗ[k] F} (hg : g ∈ M.G) {x : F} (hx : x ≠ 0)
    {a : F} (ha : a ∈ M.l) : ∃ c ∈ M.l, g (a * x) = c * g x := by
  rw [M.mem_l_iff] at ha
  induction ha using Submodule.span_induction with
  | mem a ha =>
    obtain ⟨b, hb, rfl⟩ := ha
    obtain ⟨Γ, hΓ, hxΓ⟩ := M.exists_mem_blocks (Projectivization.mk k x hx)
    have h1 : g • (b • Projectivization.mk k x hx) ∈ g • Γ :=
      Set.smul_mem_smul_set (M.Bu_smul_mem_blocks hΓ hxΓ hb)
    obtain ⟨c, hc, hcg⟩ := M.Bu_transitive (M.smul_mem_blocks hg hΓ)
      (Set.smul_mem_smul_set hxΓ) h1
    rw [units_smul_mk, smul_mk, smul_mk, smul_mk] at hcg
    obtain ⟨μ, hμ⟩ := (mk_eq_mk_iff' k _ _ _ _).mp hcg.symm
    refine ⟨algebraMap k F μ * c, M.l.mul_mem (M.l.algebraMap_mem μ) (M.coe_mem_l hc), ?_⟩
    rw [LinearEquiv.smul_def, Units.smul_def, LinearEquiv.smul_def, Algebra.smul_def,
      smul_eq_mul] at hμ
    rw [← hμ, mul_assoc]
  | zero => exact ⟨0, M.l.zero_mem, by rw [zero_mul, map_zero, zero_mul]⟩
  | add a b _ _ ha hb =>
    obtain ⟨c, hc, hca⟩ := ha
    obtain ⟨d, hd, hdb⟩ := hb
    exact ⟨c + d, M.l.add_mem hc hd, by rw [add_mul, map_add, hca, hdb, add_mul]⟩
  | smul r a _ ha =>
    obtain ⟨c, hc, hca⟩ := ha
    refine ⟨r • c, M.l.smul_mem hc, ?_⟩
    rw [smul_mul_assoc, map_smul, hca, smul_mul_assoc]

theorem normalizes_of_ne_top [Finite F] (hl : M.l ≠ ⊤) {g : F ≃ₗ[k] F} (hg : g ∈ M.G) :
    ∀ a ∈ M.l, ∃ a' ∈ M.l, ∀ x, g (a * x) = a' * g x := by
  have hgx : ∀ {x : F}, x ≠ 0 → g x ≠ 0 := fun hx h => hx (g.injective (h.trans g.map_zero.symm))
  have hφ : ∀ {x : F}, x ≠ 0 → ∀ {a : F}, a ∈ M.l → g (a * x) * (g x)⁻¹ ∈ M.l := by
    intro x hx a ha
    obtain ⟨c, hc, hca⟩ := M.exists_mem_l_mul hg hx ha
    rw [hca, mul_assoc, mul_inv_cancel₀ (hgx hx), mul_one]
    exact hc
  have hinv : ∀ {x : F}, x ≠ 0 → ∀ {c : F}, c ∈ M.l → ∃ a ∈ M.l, c * g x = g (a * x) := by
    intro x hx c hc
    obtain ⟨a, ha, hac⟩ := M.exists_mem_l_mul (M.G.inv_mem hg) (hgx hx) hc
    refine ⟨a, ha, ?_⟩
    rw [LinearEquiv.coe_inv, LinearEquiv.symm_apply_apply] at hac
    rw [← hac, LinearEquiv.apply_symm_apply]
  have hA : ∀ {x y : F}, x ≠ 0 → y ≠ 0 → y * x⁻¹ ∉ M.l → ∀ {a : F}, a ∈ M.l →
      g (a * x) * (g x)⁻¹ = g (a * y) * (g y)⁻¹ := by
    intro x y hx hy hyx a ha
    have hxy : x + y ≠ 0 := by
      intro h
      apply hyx
      rw [eq_neg_of_add_eq_zero_right h, neg_mul, mul_inv_cancel₀ hx]
      exact M.l.neg_mem M.l.one_mem
    set φx := g (a * x) * (g x)⁻¹
    set φy := g (a * y) * (g y)⁻¹
    set φs := g (a * (x + y)) * (g (x + y))⁻¹
    have ex : g (a * x) = φx * g x := by rw [mul_assoc, inv_mul_cancel₀ (hgx hx), mul_one]
    have ey : g (a * y) = φy * g y := by rw [mul_assoc, inv_mul_cancel₀ (hgx hy), mul_one]
    have es : g (a * (x + y)) = φs * g (x + y) := by
      rw [mul_assoc, inv_mul_cancel₀ (hgx hxy), mul_one]
    have key : (φs - φy) * g y = (φx - φs) * g x := by
      have := es
      rw [mul_add, map_add, map_add, ex, ey] at this
      linear_combination -this
    by_cases hsy : φs = φy
    · rw [hsy, sub_self, zero_mul] at key
      have := (mul_eq_zero.mp key.symm).resolve_right (hgx hx)
      exact sub_eq_zero.mp this
    · exfalso
      have hc : (φx - φs) * (φs - φy)⁻¹ ∈ M.l :=
        M.l.mul_mem (M.l.sub_mem (hφ hx ha) (hφ hxy ha))
          (M.l.inv_mem (M.l.sub_mem (hφ hxy ha) (hφ hy ha)))
      obtain ⟨b, hb, hbx⟩ := hinv hx hc
      have hgy : g y = g (b * x) := by
        rw [← hbx, mul_comm _ (φs - φy)⁻¹, mul_assoc, ← key, ← mul_assoc,
          inv_mul_cancel₀ (sub_ne_zero.mpr hsy), one_mul]
      have hyb : y = b * x := g.injective hgy
      apply hyx
      rw [hyb, mul_assoc, mul_inv_cancel₀ hx, mul_one]
      exact hb
  have hB : ∀ {x : F}, x ≠ 0 → ∃ z, z ≠ 0 ∧ z * x⁻¹ ∉ M.l := by
    intro x hx
    obtain ⟨t, ht⟩ : ∃ t : F, t ∉ M.l := by
      by_contra h
      push Not at h
      exact hl (eq_top_iff.mpr fun t _ => h t)
    refine ⟨t * x, mul_ne_zero (fun h => ht (h ▸ M.l.zero_mem)) hx, ?_⟩
    rwa [mul_assoc, mul_inv_cancel₀ hx, mul_one]
  intro a ha
  refine ⟨g a * (g 1)⁻¹, by simpa using hφ one_ne_zero ha, fun x => ?_⟩
  by_cases hx : x = 0
  · rw [hx, mul_zero, map_zero, mul_zero]
  have hall : g (a * x) * (g x)⁻¹ = g a * (g 1)⁻¹ := by
    by_cases hx1 : x * (1 : F)⁻¹ ∈ M.l
    · obtain ⟨z, hz, hz1⟩ := hB (one_ne_zero (α := F))
      have hzx : z * x⁻¹ ∉ M.l := by
        intro h
        apply hz1
        rw [inv_one, mul_one] at hx1 ⊢
        have := M.l.mul_mem h hx1
        rwa [mul_assoc, inv_mul_cancel₀ hx, mul_one] at this
      rw [hA hx hz hzx ha, ← hA one_ne_zero hz hz1 ha, mul_one]
    · rw [← hA one_ne_zero hx hx1 ha, mul_one]
  rw [← hall, mul_assoc, inv_mul_cancel₀ (hgx hx), mul_one]

theorem spans_of_eq_top [Finite F] (hl : M.l = ⊤) {Γ : Set (ℙ k F)} (hΓ : Γ ∈ M.blocks) :
    ⨆ p ∈ Γ, p.submodule = ⊤ := by
  obtain ⟨c₀, rfl⟩ := M.exists_units_eq hΓ
  obtain ⟨q, hq⟩ := M.nonempty
  set v := (c₀ • q).rep
  have hv : v ≠ 0 := (c₀ • q).rep_nonzero
  set W := ⨆ p ∈ c₀ • M.Δ, p.submodule
  have hmem : ∀ a : F, a ∈ Submodule.span k ((↑) '' (M.Bu : Set Fˣ) : Set F) → a * v ∈ W := by
    intro a ha
    induction ha using Submodule.span_induction with
    | mem a ha =>
      obtain ⟨b, hb, rfl⟩ := ha
      have hbp : b • (c₀ • q) ∈ c₀ • M.Δ :=
        M.Bu_smul_mem_blocks hΓ (Set.smul_mem_smul_set hq) hb
      have hle : (b • (c₀ • q)).submodule ≤ W := le_biSup (fun p => p.submodule) hbp
      apply hle
      rw [← mk_rep (c₀ • q), units_smul_mk, submodule_mk]
      exact Submodule.mem_span_singleton_self _
    | zero => rw [zero_mul]; exact W.zero_mem
    | add a b _ _ ha hb => rw [add_mul]; exact W.add_mem ha hb
    | smul r a _ ha => rw [smul_mul_assoc]; exact W.smul_mem r ha
  refine eq_top_iff.mpr fun w _ => ?_
  have h := hmem (w * v⁻¹) (M.mem_l_iff.mp (hl ▸ IntermediateField.mem_top))
  rwa [mul_assoc, inv_mul_cancel₀ hv, mul_one] at h

theorem eq_of_Bu_blocks [Finite F] {X₁ X₂ : Set (ℙ k F)} (h₁ : X₁ ⊆ M.Δ) (h₂ : X₂ ⊆ M.Δ)
    (hb₁ : ∀ c ∈ M.Bu, c • X₁ = X₁ ∨ Disjoint (c • X₁) X₁)
    (hb₂ : ∀ c ∈ M.Bu, c • X₂ = X₂ ∨ Disjoint (c • X₂) X₂) (hcard : X₁.ncard = X₂.ncard)
    {z : ℙ k F} (hz₁ : z ∈ X₁) (hz₂ : z ∈ X₂) : X₁ = X₂ := by
  have horbit : ∀ X : Set (ℙ k F), X ⊆ M.Δ → (∀ c ∈ M.Bu, c • X = X ∨ Disjoint (c • X) X) →
      z ∈ X → MulAction.orbit (MulAction.stabilizer Fˣ X) z = X := by
    intro X hX hbX hzX
    ext y
    constructor
    · rintro ⟨⟨c, hc⟩, rfl⟩
      have : c • z ∈ c • X := Set.smul_mem_smul_set hzX
      rwa [MulAction.mem_stabilizer_iff.mp hc] at this
    · intro hy
      obtain ⟨c, hc, rfl⟩ := M.Bu_transitive M.Δ_mem_blocks (hX hzX) (hX hy)
      rcases hbX c hc with h | h
      · exact ⟨⟨c, MulAction.mem_stabilizer_iff.mpr h⟩, rfl⟩
      · exact absurd hy (Set.disjoint_left.mp h (Set.smul_mem_smul_set hzX))
  have hZ : ∀ X : Set (ℙ k F), MulAction.stabilizer Fˣ z ≤ MulAction.stabilizer Fˣ X := by
    intro X c hc
    rw [MulAction.mem_stabilizer_iff] at hc ⊢
    have hk := units_smul_eq_self_iff.mp hc
    ext p
    rw [Set.mem_smul_set]
    constructor
    · rintro ⟨q, hq, rfl⟩
      rwa [units_smul_eq_self_iff.mpr hk]
    · intro hp
      exact ⟨p, hp, units_smul_eq_self_iff.mpr hk⟩
  have hcardH : ∀ X : Set (ℙ k F), X ⊆ M.Δ → (∀ c ∈ M.Bu, c • X = X ∨ Disjoint (c • X) X) →
      z ∈ X → Nat.card (MulAction.stabilizer Fˣ X) =
        Nat.card (MulAction.stabilizer Fˣ z) * X.ncard := by
    intro X hX hbX hzX
    set H := MulAction.stabilizer Fˣ X
    have hstab : MulAction.stabilizer H z = (MulAction.stabilizer Fˣ z).subgroupOf H := by
      ext h
      rw [MulAction.mem_stabilizer_iff, Subgroup.mem_subgroupOf, MulAction.mem_stabilizer_iff]
      rfl
    have h1 := (MulAction.stabilizer H z).card_mul_index
    rw [MulAction.index_stabilizer, horbit X hX hbX hzX, hstab,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe (hZ X)).toEquiv] at h1
    exact h1.symm
  have hH : MulAction.stabilizer Fˣ X₁ = MulAction.stabilizer Fˣ X₂ :=
    (IsCyclic.subgroup_eq_iff_card_eq).mpr (by
      rw [hcardH X₁ h₁ hb₁ hz₁, hcardH X₂ h₂ hb₂ hz₂, hcard])
  rw [← horbit X₁ h₁ hb₁ hz₁, ← horbit X₂ h₂ hb₂ hz₂, hH]

end MinimalBlock

end CFSG.ShultStronglyClosedTI.Singer
