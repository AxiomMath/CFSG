/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
module

public import CFSG.ThirdParty.OddOrder.Isaacs.PermutationGroups.Subdegrees
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import Mathlib.GroupTheory.SemidirectProduct

/-!
# Isaacs, Finite Group Theory — Ch. 8: `m`-arrows and the subgroups `K_m` (§8D)

Machinery for **Isaacs Thm 8.41–8.43** (pp. 249–251): `m`-arrows, the
`m`-graph components `[α]_m`, and the subgroups
`K_m(α) = ⟨G_β : β ∈ [α]_m⟩` whose indices `k_m = |K_m(α) : G_α|` drive
the common-divisor-graph theorems.

* `IsArrow G m α β` — `α → β` is an *`m`-arrow*: `β` lies in a `G_α`-orbit
  of size `m` (p. 247).  For a transitive action of a finite group this is
  symmetric (`IsArrow.symm`): equivalently `α` lies in a `G_β`-orbit of
  size `m`.
* `arrowComponent G m α` — the component `[α]_m` of `α` in the `m`-graph
  (p. 249).
* `arrowKernel G m α` — the subgroup `K_m(α) = ⟨G_β : β ∈ [α]_m⟩`.

The theorems 8.41–8.43 themselves are formalized on top of this machinery
(Thm 8.42 first, since 8.41 and 8.43 are corollaries of it).
-/

public section

namespace CFSG

namespace FiveTransitive.OddOrder.Isaacs.Ch08

open MulAction

open scoped Pointwise

variable {G Ω : Type*} [Group G] [MulAction G Ω]

section ArrowMachinery

variable (G) in
/-- `α → β` is an *`m`-arrow* if `β` lies in a `G_α`-orbit of size `m`
(Isaacs p. 247). -/
@[expose] def IsArrow (m : ℕ) (α β : Ω) : Prop :=
  Set.ncard (orbit (stabilizer G α) β) = m

lemma isArrow_iff {m : ℕ} {α β : Ω} :
    IsArrow G m α β ↔ Set.ncard (orbit (stabilizer G α) β) = m :=
  Iff.rfl

/-- For a transitive action of a finite group the `m`-arrow relation is
symmetric (Isaacs p. 247: `α → β` is an `m`-arrow iff `α` lies in a
`G_β`-orbit of size `m`). -/
lemma IsArrow.symm [Finite G] [IsPretransitive G Ω] {m : ℕ} {α β : Ω}
    (h : IsArrow G m α β) : IsArrow G m β α := by
  rw [isArrow_iff, ncard_suborbit_eq_relIndex] at h ⊢
  rw [relIndex_comm_of_card_eq (card_stabilizer_eq α β)]
  exact h

variable (G) in
/-- The component `[α]_m` of `α` in the `m`-graph (Isaacs p. 249): `α`
together with the points reachable from `α` along `m`-arrows. -/
@[expose] def arrowComponent (m : ℕ) (α : Ω) : Set Ω :=
  {β | Relation.ReflTransGen (IsArrow G m) α β}

lemma mem_arrowComponent_self (m : ℕ) (α : Ω) :
    α ∈ arrowComponent G m α :=
  Relation.ReflTransGen.refl

lemma mem_arrowComponent_of_isArrow {m : ℕ} {α β γ : Ω}
    (hβ : β ∈ arrowComponent G m α) (h : IsArrow G m β γ) :
    γ ∈ arrowComponent G m α :=
  Relation.ReflTransGen.tail hβ h

/-- Induction along the component `[α]_m`: a predicate holding at `α` and
propagating along `m`-arrows holds on all of `[α]_m`. -/
lemma arrowComponent_induction {m : ℕ} {α : Ω} {p : Ω → Prop}
    (hα : p α) (hstep : ∀ β γ : Ω, p β → IsArrow G m β γ → p γ)
    {β : Ω} (hβ : β ∈ arrowComponent G m α) : p β := by
  induction hβ with
  | refl => exact hα
  | tail _ harrow ih => exact hstep _ _ ih harrow

variable (G) in
/-- The subgroup `K_m(α) = ⟨G_β : β ∈ [α]_m⟩` (Isaacs p. 249). -/
@[expose] def arrowKernel (m : ℕ) (α : Ω) : Subgroup G :=
  Subgroup.closure (⋃ β ∈ arrowComponent G m α, (stabilizer G β : Set G))

lemma stabilizer_le_arrowKernel {m : ℕ} {α β : Ω}
    (h : β ∈ arrowComponent G m α) :
    stabilizer G β ≤ arrowKernel G m α :=
  fun _x hx => Subgroup.subset_closure (Set.mem_biUnion h hx)

lemma stabilizer_le_arrowKernel_self (m : ℕ) (α : Ω) :
    stabilizer G α ≤ arrowKernel G m α :=
  stabilizer_le_arrowKernel (mem_arrowComponent_self m α)

lemma arrowKernel_le {m : ℕ} {α : Ω} {K : Subgroup G}
    (h : ∀ β ∈ arrowComponent G m α, stabilizer G β ≤ K) :
    arrowKernel G m α ≤ K :=
  (Subgroup.closure_le K).mpr
    (Set.iUnion₂_subset fun β hβ _x hx => h β hβ hx)

lemma arrowKernel_le_arrowKernel {m n : ℕ} {α γ : Ω}
    (h : arrowComponent G m α ⊆ arrowComponent G n γ) :
    arrowKernel G m α ≤ arrowKernel G n γ :=
  arrowKernel_le fun _β hβ => stabilizer_le_arrowKernel (h hβ)

/-- `m`-arrows transport along the action. -/
lemma IsArrow.smul {m : ℕ} {α β : Ω} (h : IsArrow G m α β) (g : G) :
    IsArrow G m (g • α) (g • β) := by
  rw [isArrow_iff, ncard_suborbit_smul_eq]
  exact h

private lemma reflTransGen_isArrow_smul {m : ℕ} (g : G) {a b : Ω}
    (h : Relation.ReflTransGen (IsArrow G m) a b) :
    Relation.ReflTransGen (IsArrow G m) (g • a) (g • b) := by
  induction h with
  | refl => exact .refl
  | tail _ hbc ih => exact ih.tail (hbc.smul g)

/-- Components of the `m`-graph transport along the action
(Isaacs p. 249: `G` acts as automorphisms of the `m`-graph). -/
lemma arrowComponent_smul (m : ℕ) (g : G) (α : Ω) :
    arrowComponent G m (g • α) = (g • ·) '' arrowComponent G m α := by
  ext β
  constructor
  · intro hβ
    have h2 := reflTransGen_isArrow_smul g⁻¹ hβ
    rw [inv_smul_smul] at h2
    exact ⟨g⁻¹ • β, h2, smul_inv_smul g β⟩
  · rintro ⟨β', hβ', rfl⟩
    exact reflTransGen_isArrow_smul g hβ'

/-- The subgroups `K_m` are conjugation-equivariant (Isaacs p. 249:
`K_m(α · g) = K_m(α)^g`). -/
lemma arrowKernel_smul (m : ℕ) (g : G) (α : Ω) :
    arrowKernel G m (g • α) =
      (arrowKernel G m α).map (MulAut.conj g).toMonoidHom := by
  unfold arrowKernel
  rw [MonoidHom.map_closure]
  congr 1
  rw [arrowComponent_smul, Set.biUnion_image, Set.image_iUnion₂]
  refine Set.iUnion₂_congr fun β' _hβ' => ?_
  rw [stabilizer_smul_eq_stabilizer_map_conj, Subgroup.coe_map]

/-- The index `k_m = |K_m(α) : G_α|` does not depend on the base point
(Isaacs p. 249). -/
lemma relIndex_arrowKernel_eq [IsPretransitive G Ω] (m : ℕ) (α β : Ω) :
    (stabilizer G α).relIndex (arrowKernel G m α) =
      (stabilizer G β).relIndex (arrowKernel G m β) := by
  obtain ⟨g, rfl⟩ := exists_smul_eq G α β
  rw [stabilizer_smul_eq_stabilizer_map_conj, arrowKernel_smul,
    Subgroup.relIndex_map_map_of_injective _ _
      (MulEquiv.injective (MulAut.conj g))]

end ArrowMachinery

/-! ### Isaacs Thm 8.42 (a) -/

section Theorem842

variable [Finite G] [IsPretransitive G Ω]

/-- Every point of `[α]_m` has an `n`-arrow to `γ` when `α` does — the
`S`-closure step of Isaacs Thm 8.42, via Lem 8.39 (a), (b). -/
private lemma isArrow_of_mem_arrowComponent {m n : ℕ} {α γ : Ω}
    (hmn : m < n) (hαγ : IsArrow G n α γ)
    (hcop : ∀ δ ε : Ω,
      Nat.Coprime (Set.ncard (orbit (stabilizer G δ) ε)) m ∨
      Nat.Coprime (Set.ncard (orbit (stabilizer G δ) ε)) n)
    {β : Ω} (hβ : β ∈ arrowComponent G m α) : IsArrow G n β γ := by
  refine arrowComponent_induction (p := fun β => IsArrow G n β γ) hαγ ?_ hβ
  intro δ β' hδ harrow
  rw [isArrow_iff] at harrow
  have hδ' : Set.ncard (orbit (stabilizer G δ) γ) = n := hδ
  -- `m` and `n` are coprime
  have hcopmn : Nat.Coprime m n := by
    rcases hcop δ β' with h2 | h2 <;> rw [harrow] at h2
    · have h3 : Nat.gcd m m = 1 := h2
      rw [Nat.gcd_self] at h3
      rw [h3]
      exact Nat.coprime_one_left n
    · exact h2
  -- Lem 8.39 (a), (b) at `A = G_δ`, `B = G_{β'}`, `C = G_γ`
  have hcard : Nat.card (stabilizer G δ) = Nat.card (stabilizer G β') :=
    card_stabilizer_eq δ β'
  have hcop' : Nat.Coprime ((stabilizer G β').relIndex (stabilizer G δ))
      ((stabilizer G γ).relIndex (stabilizer G δ)) := by
    rw [← ncard_suborbit_eq_relIndex, ← ncard_suborbit_eq_relIndex,
      harrow, hδ']
    exact hcopmn
  obtain ⟨hge, hdvd⟩ := relIndex_le_and_dvd_of_coprime hcard hcop'
  rw [← ncard_suborbit_eq_relIndex, ← ncard_suborbit_eq_relIndex, hδ']
    at hge
  rw [← ncard_suborbit_eq_relIndex, ← ncard_suborbit_eq_relIndex,
    ← ncard_suborbit_eq_relIndex, harrow, hδ'] at hdvd
  -- the arrow value `β' → γ` is a subdegree coprime to `m` or `n`
  rw [isArrow_iff]
  rcases hcop β' γ with h2 | h2
  · -- coprime to `m`: it divides `n`, and is `≥ n`
    have h3 := Nat.Coprime.dvd_of_dvd_mul_left h2 hdvd
    exact Nat.le_antisymm (Nat.le_of_dvd (by omega) h3) hge
  · -- coprime to `n`: it divides `m`, contradicting `≥ n > m`
    exfalso
    have h3 := Nat.Coprime.dvd_of_dvd_mul_right h2 hdvd
    have h4 : 0 < m := by
      have h5 : (orbit (stabilizer G δ) β').Finite := Set.finite_range _
      have h6 := (Set.ncard_pos h5).mpr ⟨β', mem_orbit_self _⟩
      omega
    have h7 := Nat.le_of_dvd h4 h3
    omega

/-- **Isaacs Thm 8.42 (a)** (p. 250) — let a finite group `G` act
transitively on `Ω`, let `m < n` be subdegrees such that every subdegree
is coprime to `m` or to `n`, and let `α → γ` be an `n`-arrow.  Then
`k_m = |K_m(α) : G_α|` divides `k_n = |K_n(γ) : G_γ|`. -/
theorem relIndex_arrowKernel_dvd_relIndex_arrowKernel {m n : ℕ} {α γ : Ω}
    (hmn : m < n) (hαγ : IsArrow G n α γ)
    (hcop : ∀ δ ε : Ω,
      Nat.Coprime (Set.ncard (orbit (stabilizer G δ) ε)) m ∨
      Nat.Coprime (Set.ncard (orbit (stabilizer G δ) ε)) n) :
    (stabilizer G α).relIndex (arrowKernel G m α) ∣
      (stabilizer G γ).relIndex (arrowKernel G n γ) := by
  -- `[α]_m ⊆ [γ]_n`, hence `K_m(α) ≤ K_n(γ)`
  have hcompsub : arrowComponent G m α ⊆ arrowComponent G n γ := by
    intro β hβ
    exact mem_arrowComponent_of_isArrow (mem_arrowComponent_self n γ)
      (isArrow_of_mem_arrowComponent hmn hαγ hcop hβ).symm
  have hK : arrowKernel G m α ≤ arrowKernel G n γ :=
    arrowKernel_le_arrowKernel hcompsub
  set Km := arrowKernel G m α
  set Kn := arrowKernel G n γ
  -- index tower: `k_n = |K_n : K_m| · k_m`
  have h1 : (stabilizer G α).relIndex Km * Nat.card (stabilizer G α) =
      Nat.card Km := by
    have h4 := relIndex_mul_card_inf (stabilizer G α) Km
    rwa [inf_eq_left.mpr (stabilizer_le_arrowKernel_self m α)] at h4
  have h2 : (stabilizer G γ).relIndex Kn * Nat.card (stabilizer G γ) =
      Nat.card Kn := by
    have h4 := relIndex_mul_card_inf (stabilizer G γ) Kn
    rwa [inf_eq_left.mpr (stabilizer_le_arrowKernel_self n γ)] at h4
  have h3 : Km.relIndex Kn * Nat.card Km = Nat.card Kn := by
    have h4 := relIndex_mul_card_inf Km Kn
    rwa [inf_eq_left.mpr hK] at h4
  have hstab : Nat.card (stabilizer G α) = Nat.card (stabilizer G γ) :=
    card_stabilizer_eq α γ
  have hpos : 0 < Nat.card (stabilizer G γ) := Nat.card_pos
  have h6 : (stabilizer G γ).relIndex Kn * Nat.card (stabilizer G γ) =
      Km.relIndex Kn * (stabilizer G α).relIndex Km *
        Nat.card (stabilizer G γ) := by
    rw [h2, ← h3, ← h1, hstab, mul_assoc]
  have h7 : (stabilizer G γ).relIndex Kn =
      Km.relIndex Kn * (stabilizer G α).relIndex Km :=
    Nat.eq_of_mul_eq_mul_right hpos h6
  exact Dvd.intro_left _ h7.symm

/-- Counting the image of a subgroup in a coset space:
`|mk '' A| = |A : C ∩ A|` in `M ⧸ C`. -/
private lemma ncard_image_mk_eq_relIndex {M : Type*} [Group M] [Finite M]
    (C A : Subgroup M) :
    Set.ncard ((QuotientGroup.mk : M → M ⧸ C) '' (A : Set M)) =
      C.relIndex A := by
  have hstab : stabilizer (↥A) ((1 : M) : M ⧸ C) = C.subgroupOf A := by
    ext x
    rw [mem_stabilizer_iff, Subgroup.mem_subgroupOf]
    have hkey : (x • ((1 : M) : M ⧸ C) = ((1 : M) : M ⧸ C)) ↔
        ((↑x * 1 : M) : M ⧸ C) = ((1 : M) : M ⧸ C) := Iff.rfl
    rw [hkey, mul_one, QuotientGroup.eq, mul_one, inv_mem_iff]
  have horb : (QuotientGroup.mk : M → M ⧸ C) '' (A : Set M) =
      orbit (↥A) ((1 : M) : M ⧸ C) := by
    ext x
    constructor
    · rintro ⟨a, ha, rfl⟩
      rw [MulAction.mem_orbit_iff]
      refine ⟨⟨a, ha⟩, ?_⟩
      have h2 : (⟨a, ha⟩ : ↥A) • ((1 : M) : M ⧸ C) =
          ((a * 1 : M) : M ⧸ C) := rfl
      rw [h2, mul_one]
    · rintro ⟨a, ha⟩
      have ha' : a • ((1 : M) : M ⧸ C) = x := ha
      rw [← ha']
      have h2 : a • ((1 : M) : M ⧸ C) = ((↑a * 1 : M) : M ⧸ C) := rfl
      rw [h2, mul_one]
      exact ⟨↑a, a.2, rfl⟩
  rw [horb, ← Nat.card_coe_set_eq,
    Nat.card_congr (orbitEquivQuotientStabilizer (↥A) ((1 : M) : M ⧸ C)),
    hstab]
  rfl

/-- If `C A = C B` (as subsets) then `|A : C ∩ A| = |B : C ∩ B|`. -/
private lemma relIndex_eq_of_coe_mul_eq {M : Type*} [Group M] [Finite M]
    {C A B : Subgroup M}
    (h : (C : Set M) * (A : Set M) = (C : Set M) * (B : Set M)) :
    C.relIndex A = C.relIndex B := by
  -- pass to `A C = B C` by taking inverses
  have h2 : (A : Set M) * (C : Set M) = (B : Set M) * (C : Set M) := by
    have h3 := congrArg (·⁻¹) h
    simpa only [mul_inv_rev, inv_coe_set] using h3
  have himg : ∀ {A' B' : Subgroup M},
      (A' : Set M) * (C : Set M) = (B' : Set M) * (C : Set M) →
      (QuotientGroup.mk : M → M ⧸ C) '' (A' : Set M) ⊆
        QuotientGroup.mk '' (B' : Set M) := by
    intro A' B' hAB
    rintro x ⟨a, ha, rfl⟩
    have h4 : (a : M) ∈ (B' : Set M) * (C : Set M) := by
      rw [← hAB, Set.mem_mul]
      exact ⟨a, ha, 1, C.one_mem, mul_one a⟩
    rw [Set.mem_mul] at h4
    obtain ⟨b, hb, c, hc, hbc⟩ := h4
    refine ⟨b, hb, ?_⟩
    rw [QuotientGroup.eq, ← hbc, ← mul_assoc, inv_mul_cancel, one_mul]
    exact hc
  rw [← ncard_image_mk_eq_relIndex C A, ← ncard_image_mk_eq_relIndex C B]
  congr 1
  exact Set.Subset.antisymm (himg h2) (himg h2.symm)

/-- **Isaacs Thm 8.42 (b)** (p. 250) — with hypotheses as in (a),
`k_m = |K_m(α) : G_α|` divides `n`. -/
theorem relIndex_arrowKernel_dvd_of_isArrow {m n : ℕ} {α γ : Ω}
    (hmn : m < n) (hαγ : IsArrow G n α γ)
    (hcop : ∀ δ ε : Ω,
      Nat.Coprime (Set.ncard (orbit (stabilizer G δ) ε)) m ∨
      Nat.Coprime (Set.ncard (orbit (stabilizer G δ) ε)) n) :
    (stabilizer G α).relIndex (arrowKernel G m α) ∣ n := by
  set T : Set G := (stabilizer G γ : Set G) * (stabilizer G α : Set G)
    with hTdef
  -- (b1): `C G_δ = C G_α` for every `δ ∈ [α]_m`, via Lem 8.39(c) both ways
  have hb1 : ∀ δ ∈ arrowComponent G m α,
      δ ∈ arrowComponent G m α ∧
        (stabilizer G γ : Set G) * (stabilizer G δ : Set G) = T := by
    intro δ hδ
    refine arrowComponent_induction
      (p := fun δ => δ ∈ arrowComponent G m α ∧
        (stabilizer G γ : Set G) * (stabilizer G δ : Set G) = T)
      ⟨mem_arrowComponent_self m α, hTdef.symm⟩ ?_ hδ
    rintro β β' ⟨hβmem, hIH⟩ harrow
    refine ⟨mem_arrowComponent_of_isArrow hβmem harrow, ?_⟩
    have hSβ : IsArrow G n β γ :=
      isArrow_of_mem_arrowComponent hmn hαγ hcop hβmem
    have hSβ' : IsArrow G n β' γ :=
      isArrow_of_mem_arrowComponent hmn hαγ hcop
        (mem_arrowComponent_of_isArrow hβmem harrow)
    have harrow' : Set.ncard (orbit (stabilizer G β') β) = m :=
      harrow.symm
    rw [isArrow_iff] at harrow hSβ hSβ'
    -- coprimality of `m` and `n`
    have hcopmn : Nat.Coprime m n := by
      rcases hcop β β' with h2 | h2 <;> rw [harrow] at h2
      · have h3 : Nat.gcd m m = 1 := h2
        rw [Nat.gcd_self] at h3
        rw [h3]
        exact Nat.coprime_one_left n
      · exact h2
    -- Lem 8.39(c) forwards: `C G_β ⊆ C G_{β'}`
    have hfwd : (stabilizer G γ : Set G) * (stabilizer G β : Set G) ⊆
        (stabilizer G γ : Set G) * (stabilizer G β' : Set G) := by
      apply mul_subset_mul_of_coprime
      rw [← ncard_suborbit_eq_relIndex, ← ncard_suborbit_eq_relIndex,
        harrow, hSβ]
      exact hcopmn
    -- Lem 8.39(c) backwards: `C G_{β'} ⊆ C G_β`
    have hbwd : (stabilizer G γ : Set G) * (stabilizer G β' : Set G) ⊆
        (stabilizer G γ : Set G) * (stabilizer G β : Set G) := by
      apply mul_subset_mul_of_coprime
      rw [← ncard_suborbit_eq_relIndex, ← ncard_suborbit_eq_relIndex,
        harrow', hSβ']
      exact hcopmn
    rw [← hIH]
    exact Set.Subset.antisymm hbwd hfwd
  -- (b2): `T` is invariant under right multiplication by each `G_δ`
  have hTg : ∀ δ ∈ arrowComponent G m α, ∀ g ∈ stabilizer G δ,
      T * {g} ⊆ T := by
    intro δ hδ g hg z hz
    have hTδ := (hb1 δ hδ).2
    rw [Set.mem_mul] at hz
    obtain ⟨t, ht, g', hg', htg⟩ := hz
    rw [Set.mem_singleton_iff] at hg'
    rw [hg'] at htg
    rw [← hTδ, Set.mem_mul] at ht
    obtain ⟨c, hc, d, hd, hcd⟩ := ht
    rw [← htg, ← hcd, ← hTδ, Set.mem_mul]
    exact ⟨c, hc, d * g, (stabilizer G δ).mul_mem hd hg,
      (mul_assoc c d g).symm⟩
  have hTg' : ∀ δ ∈ arrowComponent G m α, ∀ g ∈ stabilizer G δ,
      T * {g} = T := by
    intro δ hδ g hg
    apply Set.Subset.antisymm (hTg δ hδ g hg)
    intro t ht
    have h2 : t * g⁻¹ ∈ T := by
      apply hTg δ hδ g⁻¹ (inv_mem hg)
      rw [Set.mem_mul]
      exact ⟨t, ht, g⁻¹, rfl, rfl⟩
    rw [Set.mem_mul]
    exact ⟨t * g⁻¹, h2, g, rfl,
      by rw [mul_assoc, inv_mul_cancel, mul_one]⟩
  -- (b3): hence invariant under right multiplication by `K_m(α)`
  have hTK : ∀ g ∈ arrowKernel G m α, T * {g} = T := by
    intro g hgK
    have hgK' : g ∈ Subgroup.closure
        (⋃ β ∈ arrowComponent G m α, (stabilizer G β : Set G)) := hgK
    clear hgK
    induction hgK' using Subgroup.closure_induction with
    | mem x hx =>
      obtain ⟨δ, hδ, hxδ⟩ := Set.mem_iUnion₂.mp hx
      exact hTg' δ hδ x hxδ
    | one =>
      rw [show ({1} : Set G) = (1 : Set G) from rfl, mul_one]
    | mul x y hx hy hTx hTy =>
      rw [← Set.singleton_mul_singleton, ← mul_assoc, hTx, hTy]
    | inv x hx hTx =>
      calc T * {x⁻¹} = (T * {x}) * {x⁻¹} := by rw [hTx]
        _ = T * ({x} * {x⁻¹}) := by rw [mul_assoc]
        _ = T * {1} := by
            rw [Set.singleton_mul_singleton, mul_inv_cancel]
        _ = T := by
            rw [show ({1} : Set G) = (1 : Set G) from rfl, mul_one]
  -- (b4): `C K_m(α) = C G_α`
  have hTK2 : T * (arrowKernel G m α : Set G) = T := by
    apply Set.Subset.antisymm
    · rintro z hz
      rw [Set.mem_mul] at hz
      obtain ⟨t, ht, k, hk, htk⟩ := hz
      rw [← hTK k hk, Set.mem_mul]
      exact ⟨t, ht, k, rfl, htk⟩
    · intro t ht
      rw [Set.mem_mul]
      exact ⟨t, ht, 1, (arrowKernel G m α).one_mem, mul_one t⟩
  have hCK : (stabilizer G γ : Set G) * (arrowKernel G m α : Set G) =
      T := by
    apply Set.Subset.antisymm
    · rintro z hz
      rw [Set.mem_mul] at hz
      obtain ⟨c, hc, k, hk, hck⟩ := hz
      have hcT : c ∈ T := by
        rw [Set.mem_mul]
        exact ⟨c, hc, 1, (stabilizer G α).one_mem, mul_one c⟩
      rw [← hTK2, Set.mem_mul]
      exact ⟨c, hcT, k, hk, hck⟩
    · rintro z hz
      rw [Set.mem_mul] at hz ⊢
      obtain ⟨c, hc, a, ha, hca⟩ := hz
      exact ⟨c, hc, a, stabilizer_le_arrowKernel_self m α ha, hca⟩
  -- (b5): index bookkeeping — `n = k_m · |G_γ : G_γ ∩ K|`
  have hrel : (stabilizer G γ).relIndex (arrowKernel G m α) =
      (stabilizer G γ).relIndex (stabilizer G α) :=
    relIndex_eq_of_coe_mul_eq (by rw [hCK, hTdef])
  have hn : (stabilizer G γ).relIndex (stabilizer G α) = n := by
    rw [← ncard_suborbit_eq_relIndex]
    exact hαγ
  set K := arrowKernel G m α
  set C := stabilizer G γ
  set A := stabilizer G α
  have h1 : C.relIndex K * Nat.card ↥(C ⊓ K) = Nat.card K :=
    relIndex_mul_card_inf C K
  have h2 : A.relIndex K * Nat.card A = Nat.card K := by
    have h4 := relIndex_mul_card_inf A K
    rwa [inf_eq_left.mpr (stabilizer_le_arrowKernel_self m α)] at h4
  have h3 : K.relIndex C * Nat.card ↥(K ⊓ C) = Nat.card C :=
    relIndex_mul_card_inf K C
  have hAC : Nat.card A = Nat.card C := card_stabilizer_eq α γ
  have h5 : n * Nat.card ↥(C ⊓ K) =
      A.relIndex K * K.relIndex C * Nat.card ↥(C ⊓ K) := by
    rw [← hn, ← hrel, h1, ← h2, hAC, ← h3, inf_comm K C, ← mul_assoc]
  have hpos : 0 < Nat.card ↥(C ⊓ K) := Nat.card_pos
  have h6 : n = A.relIndex K * K.relIndex C :=
    Nat.eq_of_mul_eq_mul_right hpos h5
  exact ⟨K.relIndex C, h6⟩

/-! ### Isaacs Thm 8.41 — the common-divisor graph -/

/-- The remark before Thm 8.42 (Isaacs p. 249): an `m`-arrow with `m > 1`
forces `k_m > 1`. -/
lemma one_lt_relIndex_arrowKernel_of_isArrow {m : ℕ} {α β : Ω}
    (hm : 1 < m) (h : IsArrow G m α β) :
    1 < (stabilizer G α).relIndex (arrowKernel G m α) := by
  have hne : (stabilizer G α).relIndex (arrowKernel G m α) ≠ 0 :=
    Subgroup.index_ne_zero_of_finite
  rcases Nat.lt_or_ge 1 ((stabilizer G α).relIndex (arrowKernel G m α))
    with h2 | h2
  · exact h2
  · exfalso
    have h3 : (stabilizer G α).relIndex (arrowKernel G m α) = 1 := by omega
    have h4 : arrowKernel G m α ≤ stabilizer G α := by
      have h5 : (stabilizer G α).subgroupOf (arrowKernel G m α) = ⊤ := by
        rw [← Subgroup.index_eq_one]
        exact h3
      exact Subgroup.subgroupOf_eq_top.mp h5
    have h7 : stabilizer G β ≤ stabilizer G α :=
      le_trans (stabilizer_le_arrowKernel
        (mem_arrowComponent_of_isArrow (mem_arrowComponent_self m α) h)) h4
    have h8 : stabilizer G β = stabilizer G α :=
      Subgroup.eq_of_le_of_card_ge h7 (le_of_eq (card_stabilizer_eq α β))
    have h9 : orbit (stabilizer G α) β = {β} := by
      rw [← h8]
      exact orbit_stabilizer_self β
    have h10 : Set.ncard (orbit (stabilizer G α) β) = m := h
    rw [h9, Set.ncard_singleton] at h10
    omega

/-- Core of **Isaacs Thm 8.41** — three subdegrees `u < v, w` with `v, w`
coprime, such that every subdegree is coprime to `u` or `v`, and to `u`
or `w`, force `u = 1`. -/
theorem subdegree_eq_one_of_separations {u v w : ℕ} {α βu βv βw : Ω}
    (hu : IsArrow G u α βu) (hv : IsArrow G v α βv)
    (hw : IsArrow G w α βw)
    (huv : u < v) (huw : u < w) (hvw : Nat.Coprime v w)
    (hsepv : ∀ δ ε : Ω,
      Nat.Coprime (Set.ncard (orbit (stabilizer G δ) ε)) u ∨
      Nat.Coprime (Set.ncard (orbit (stabilizer G δ) ε)) v)
    (hsepw : ∀ δ ε : Ω,
      Nat.Coprime (Set.ncard (orbit (stabilizer G δ) ε)) u ∨
      Nat.Coprime (Set.ncard (orbit (stabilizer G δ) ε)) w) :
    u = 1 := by
  by_contra hu1
  have hu0 : 0 < u := by
    have h5 : (orbit (stabilizer G α) βu).Finite := Set.finite_range _
    have h6 := (Set.ncard_pos h5).mpr ⟨βu, mem_orbit_self _⟩
    have hu' : Set.ncard (orbit (stabilizer G α) βu) = u := hu
    omega
  have hu2 : 1 < u := by omega
  have h1 := relIndex_arrowKernel_dvd_of_isArrow huv hv hsepv
  have h2 := relIndex_arrowKernel_dvd_of_isArrow huw hw hsepw
  have h3 : (stabilizer G α).relIndex (arrowKernel G u α) ∣ Nat.gcd v w :=
    Nat.dvd_gcd h1 h2
  have hvw' : Nat.gcd v w = 1 := hvw
  rw [hvw'] at h3
  have h4 := Nat.dvd_one.mp h3
  have h5 := one_lt_relIndex_arrowKernel_of_isArrow hu2 hu
  omega

omit [Finite G] in
/-- Transport of a subdegree witness to any base point. -/
lemma IsArrow.exists_of_point {d : ℕ} {δ ε : Ω}
    (h : IsArrow G d δ ε) (α : Ω) : ∃ β, IsArrow G d α β := by
  obtain ⟨g, rfl⟩ := exists_smul_eq G δ α
  refine ⟨g • ε, ?_⟩
  rw [isArrow_iff, ncard_suborbit_smul_eq]
  exact h

end Theorem842

section CommonDivisorGraphDef

variable (G Ω) in
/-- The set of subdegrees of the action. -/
@[expose] def subdegrees : Set ℕ := {d | ∃ α β : Ω, IsArrow G d α β}

/-- The common-divisor graph on a set of naturals (Isaacs p. 249):
distinct `a, b` are joined when they are *not* coprime. -/
@[expose] def commonDivisorGraph (D : Set ℕ) : SimpleGraph D where
  Adj a b := a ≠ b ∧ ¬ Nat.Coprime (a : ℕ) (b : ℕ)
  symm := by
    constructor
    rintro a b ⟨hab, hcop⟩
    exact ⟨hab.symm, fun h => hcop (Nat.Coprime.symm h)⟩
  loopless := by
    constructor
    rintro a ⟨hab, -⟩
    exact hab rfl

/-- Every subdegree is positive. -/
lemma subdegrees_pos [Finite G] (d : ↥(subdegrees G Ω)) : 0 < (d : ℕ) := by
  obtain ⟨α, β, h⟩ := d.2
  have h5 : (orbit (stabilizer G α) β).Finite := Set.finite_range _
  have h6 := (Set.ncard_pos h5).mpr ⟨β, mem_orbit_self _⟩
  have h' : Set.ncard (orbit (stabilizer G α) β) = (d : ℕ) := h
  omega

/-- Vertices of the common-divisor graph in different components separate
the subdegree set: every subdegree is coprime to one of the two. -/
lemma separation_of_connectedComponentMk_ne {a b : ↥(subdegrees G Ω)}
    (hab : (commonDivisorGraph (subdegrees G Ω)).connectedComponentMk a ≠
      (commonDivisorGraph (subdegrees G Ω)).connectedComponentMk b) :
    ∀ δ ε : Ω,
      Nat.Coprime (Set.ncard (orbit (stabilizer G δ) ε)) (a : ℕ) ∨
      Nat.Coprime (Set.ncard (orbit (stabilizer G δ) ε)) (b : ℕ) := by
  intro δ ε
  by_contra hcon
  push Not at hcon
  obtain ⟨h1, h2⟩ := hcon
  have hdD : Set.ncard (orbit (stabilizer G δ) ε) ∈ subdegrees G Ω :=
    ⟨δ, ε, rfl⟩
  set d : ↥(subdegrees G Ω) := ⟨Set.ncard (orbit (stabilizer G δ) ε), hdD⟩
    with hd
  have hne_ab : a ≠ b := fun h => hab (by rw [h])
  by_cases hda : d = a
  · have hadj : (commonDivisorGraph (subdegrees G Ω)).Adj a b := by
      refine ⟨hne_ab, ?_⟩
      rw [← hda]
      exact h2
    exact hab (SimpleGraph.ConnectedComponent.eq.mpr hadj.reachable)
  · by_cases hdb : d = b
    · have hadj : (commonDivisorGraph (subdegrees G Ω)).Adj a b := by
        refine ⟨hne_ab, ?_⟩
        have h3 : ¬ Nat.Coprime (b : ℕ) (a : ℕ) := by
          rw [← hdb]
          exact h1
        exact fun h => h3 (Nat.Coprime.symm h)
      exact hab (SimpleGraph.ConnectedComponent.eq.mpr hadj.reachable)
    · have hadj1 : (commonDivisorGraph (subdegrees G Ω)).Adj d a := ⟨hda, h1⟩
      have hadj2 : (commonDivisorGraph (subdegrees G Ω)).Adj d b := ⟨hdb, h2⟩
      have hreach : (commonDivisorGraph (subdegrees G Ω)).Reachable a b :=
        (hadj1.reachable.symm).trans hadj2.reachable
      exact hab (SimpleGraph.ConnectedComponent.eq.mpr hreach)

/-- Vertices of the common-divisor graph in different components are
coprime. -/
lemma coprime_of_connectedComponentMk_ne {a b : ↥(subdegrees G Ω)}
    (hab : (commonDivisorGraph (subdegrees G Ω)).connectedComponentMk a ≠
      (commonDivisorGraph (subdegrees G Ω)).connectedComponentMk b) :
    Nat.Coprime (a : ℕ) (b : ℕ) := by
  by_contra h2
  have hadj : (commonDivisorGraph (subdegrees G Ω)).Adj a b :=
    ⟨fun h => hab (by rw [h]), h2⟩
  exact hab (SimpleGraph.ConnectedComponent.eq.mpr hadj.reachable)

end CommonDivisorGraphDef

section Theorem841

variable [Finite G] [IsPretransitive G Ω] [Nonempty Ω]

/-- **Isaacs Thm 8.41** (p. 249) — the common-divisor graph on the set of
subdegrees of a transitive action of a finite group has at most three
connected components (including the component `{1}`). -/
theorem card_connectedComponent_commonDivisorGraph_le_three :
    Nat.card
      (commonDivisorGraph (subdegrees G Ω)).ConnectedComponent ≤ 3 := by
  classical
  by_contra hlt
  rw [not_le] at hlt
  set D := subdegrees G Ω with hD
  set Γ := commonDivisorGraph D with hΓ
  obtain ⟨α₀⟩ := ‹Nonempty Ω›
  have h1D : (1 : ℕ) ∈ D := by
    refine ⟨α₀, α₀, ?_⟩
    rw [isArrow_iff, orbit_stabilizer_self, Set.ncard_singleton]
  set one : ↥D := ⟨1, h1D⟩ with hone
  set comp1 := Γ.connectedComponentMk one with hcomp1
  -- three vertices in distinct components, none the component of `1`
  have hkey : ∀ x y z : ↥D,
      Γ.connectedComponentMk x ≠ Γ.connectedComponentMk y →
      Γ.connectedComponentMk x ≠ Γ.connectedComponentMk z →
      Γ.connectedComponentMk y ≠ Γ.connectedComponentMk z →
      Γ.connectedComponentMk x ≠ comp1 →
      Γ.connectedComponentMk y ≠ comp1 →
      Γ.connectedComponentMk z ≠ comp1 → False := by
    intro x y z hxy hxz hyz hx1 hy1 hz1
    have hval1 : ∀ t : ↥D, (t : ℕ) = 1 →
        Γ.connectedComponentMk t = comp1 := by
      intro t ht
      have h2 : t = one := Subtype.ext (by rw [ht])
      rw [h2, hcomp1]
    obtain ⟨δx, εx, hx⟩ := x.2
    obtain ⟨βx, hx'⟩ := hx.exists_of_point α₀
    obtain ⟨δy, εy, hy⟩ := y.2
    obtain ⟨βy, hy'⟩ := hy.exists_of_point α₀
    obtain ⟨δz, εz, hz⟩ := z.2
    obtain ⟨βz, hz'⟩ := hz.exists_of_point α₀
    have hvxy : (x : ℕ) ≠ (y : ℕ) := fun h2 => hxy (by rw [Subtype.ext h2])
    have hvxz : (x : ℕ) ≠ (z : ℕ) := fun h2 => hxz (by rw [Subtype.ext h2])
    have hvyz : (y : ℕ) ≠ (z : ℕ) := fun h2 => hyz (by rw [Subtype.ext h2])
    have hsxy := separation_of_connectedComponentMk_ne hxy
    have hsxz := separation_of_connectedComponentMk_ne hxz
    have hsyz := separation_of_connectedComponentMk_ne hyz
    have hcxy := coprime_of_connectedComponentMk_ne hxy
    have hcxz := coprime_of_connectedComponentMk_ne hxz
    have hcyz := coprime_of_connectedComponentMk_ne hyz
    rcases Nat.lt_trichotomy (x : ℕ) (y : ℕ) with h12 | h12 | h12
    · rcases Nat.lt_trichotomy (x : ℕ) (z : ℕ) with h13 | h13 | h13
      · -- `x` smallest
        exact hx1 (hval1 x
          (subdegree_eq_one_of_separations hx' hy' hz' h12 h13 hcyz
            hsxy hsxz))
      · exact hvxz h13
      · -- `z < x < y`: `z` smallest
        exact hz1 (hval1 z
          (subdegree_eq_one_of_separations hz' hx' hy' h13
            (lt_trans h13 h12) hcxy
            (fun δ ε => (hsxz δ ε).symm) (fun δ ε => (hsyz δ ε).symm)))
    · exact hvxy h12
    · rcases Nat.lt_trichotomy (y : ℕ) (z : ℕ) with h23 | h23 | h23
      · -- `y` smallest
        exact hy1 (hval1 y
          (subdegree_eq_one_of_separations hy' hx' hz' h12 h23 hcxz
            (fun δ ε => (hsxy δ ε).symm) hsyz))
      · exact hvyz h23
      · -- `z < y < x`: `z` smallest
        exact hz1 (hval1 z
          (subdegree_eq_one_of_separations hz' hx' hy'
            (lt_trans h23 h12) h23 hcxy
            (fun δ ε => (hsxz δ ε).symm) (fun δ ε => (hsyz δ ε).symm)))
  -- extract four distinct components
  have hfin : Finite Γ.ConnectedComponent := by
    rcases finite_or_infinite Γ.ConnectedComponent with h | h
    · exact h
    · have := h
      rw [Nat.card_eq_zero_of_infinite] at hlt
      omega
  have := hfin
  have := Fintype.ofFinite Γ.ConnectedComponent
  have hcard : 3 < (Finset.univ : Finset Γ.ConnectedComponent).card := by
    rwa [Finset.card_univ, ← Nat.card_eq_fintype_card]
  obtain ⟨c₁, -⟩ := Finset.card_pos.mp (by omega : 0 < (Finset.univ :
    Finset Γ.ConnectedComponent).card)
  have h2 : 0 < (Finset.univ.erase c₁).card := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ c₁)]
    omega
  obtain ⟨c₂, hc₂⟩ := Finset.card_pos.mp h2
  have hc₂1 : c₂ ≠ c₁ := (Finset.mem_erase.mp hc₂).1
  have h3 : 0 < ((Finset.univ.erase c₁).erase c₂).card := by
    rw [Finset.card_erase_of_mem hc₂,
      Finset.card_erase_of_mem (Finset.mem_univ c₁)]
    omega
  obtain ⟨c₃, hc₃⟩ := Finset.card_pos.mp h3
  have hc₃2 : c₃ ≠ c₂ := (Finset.mem_erase.mp hc₃).1
  have hc₃1 : c₃ ≠ c₁ :=
    (Finset.mem_erase.mp (Finset.mem_erase.mp hc₃).2).1
  have h4 : 0 < (((Finset.univ.erase c₁).erase c₂).erase c₃).card := by
    rw [Finset.card_erase_of_mem hc₃, Finset.card_erase_of_mem hc₂,
      Finset.card_erase_of_mem (Finset.mem_univ c₁)]
    omega
  obtain ⟨c₄, hc₄⟩ := Finset.card_pos.mp h4
  have hc₄3 : c₄ ≠ c₃ := (Finset.mem_erase.mp hc₄).1
  have hc₄2 : c₄ ≠ c₂ :=
    (Finset.mem_erase.mp (Finset.mem_erase.mp hc₄).2).1
  have hc₄1 : c₄ ≠ c₁ :=
    (Finset.mem_erase.mp
      (Finset.mem_erase.mp (Finset.mem_erase.mp hc₄).2).2).1
  -- three of them avoid `comp1`
  have hpick : ∃ d₁ d₂ d₃ : Γ.ConnectedComponent,
      d₁ ≠ d₂ ∧ d₁ ≠ d₃ ∧ d₂ ≠ d₃ ∧
        d₁ ≠ comp1 ∧ d₂ ≠ comp1 ∧ d₃ ≠ comp1 := by
    by_cases h1 : c₁ = comp1
    · exact ⟨c₂, c₃, c₄, fun h => hc₃2 h.symm, fun h => hc₄2 h.symm,
        fun h => hc₄3 h.symm, h1 ▸ hc₂1, h1 ▸ hc₃1, h1 ▸ hc₄1⟩
    · by_cases h2' : c₂ = comp1
      · exact ⟨c₁, c₃, c₄, fun h => hc₃1 h.symm, fun h => hc₄1 h.symm,
          fun h => hc₄3 h.symm, h1, h2' ▸ hc₃2, h2' ▸ hc₄2⟩
      · by_cases h3' : c₃ = comp1
        · exact ⟨c₁, c₂, c₄, fun h => hc₂1 h.symm, fun h => hc₄1 h.symm,
            fun h => hc₄2 h.symm, h1, h2', h3' ▸ hc₄3⟩
        · exact ⟨c₁, c₂, c₃, fun h => hc₂1 h.symm, fun h => hc₃1 h.symm,
            fun h => hc₃2 h.symm, h1, h2', h3'⟩
  obtain ⟨d₁, d₂, d₃, h12, h13, h23, hd1, hd2, hd3⟩ := hpick
  obtain ⟨x, rfl⟩ := Quot.exists_rep d₁
  obtain ⟨y, rfl⟩ := Quot.exists_rep d₂
  obtain ⟨z, rfl⟩ := Quot.exists_rep d₃
  exact hkey x y z h12 h13 h23 hd1 hd2 hd3

end Theorem841

/-! ### Isaacs Thm 8.43 -/

section Theorem843

variable [Finite G] [IsPretransitive G Ω]

/-- **Isaacs Thm 8.43** (p. 251) — let `cA ≠ cB` be two components of the
common-divisor graph of the subdegrees, neither containing `1`, and
suppose `cB` contains the largest subdegree `ν`.  Then every subdegree in
`cA` is smaller than every subdegree in `cB`, and every two distinct
subdegrees in `cB` fail to be coprime (are joined by an edge).

(The book states this for a graph with exactly three components
`{1}, A, B`; the hypothesis that these are all the components is not
needed for the proof.) -/
theorem lt_forall_and_not_coprime_of_max_mem
    {cA cB : (commonDivisorGraph (subdegrees G Ω)).ConnectedComponent}
    (hAB : cA ≠ cB)
    (hA1 : ∀ t : ↥(subdegrees G Ω),
      (commonDivisorGraph (subdegrees G Ω)).connectedComponentMk t = cA →
      (t : ℕ) ≠ 1)
    (hB1 : ∀ t : ↥(subdegrees G Ω),
      (commonDivisorGraph (subdegrees G Ω)).connectedComponentMk t = cB →
      (t : ℕ) ≠ 1)
    {ν : ↥(subdegrees G Ω)}
    (hν : (commonDivisorGraph (subdegrees G Ω)).connectedComponentMk ν = cB)
    (hmax : ∀ d : ↥(subdegrees G Ω), (d : ℕ) ≤ (ν : ℕ)) :
    (∀ a b : ↥(subdegrees G Ω),
      (commonDivisorGraph (subdegrees G Ω)).connectedComponentMk a = cA →
      (commonDivisorGraph (subdegrees G Ω)).connectedComponentMk b = cB →
      (a : ℕ) < (b : ℕ)) ∧
    (∀ u v : ↥(subdegrees G Ω),
      (commonDivisorGraph (subdegrees G Ω)).connectedComponentMk u = cB →
      (commonDivisorGraph (subdegrees G Ω)).connectedComponentMk v = cB →
      u ≠ v → ¬ Nat.Coprime (u : ℕ) (v : ℕ)) := by
  classical
  -- a fixed base point for all the indices `k_m`
  obtain ⟨α₀, -, -⟩ := ν.2
  -- value inequality from distinct components
  have hvalne : ∀ s t : ↥(subdegrees G Ω),
      (commonDivisorGraph (subdegrees G Ω)).connectedComponentMk s ≠
        (commonDivisorGraph (subdegrees G Ω)).connectedComponentMk t →
      (s : ℕ) ≠ (t : ℕ) :=
    fun _s _t hst h2 => hst (by rw [Subtype.ext h2])
  -- `k_s ∣ t` for `s < t` in different components (Thm 8.42 (b))
  have hkdvd : ∀ s t : ↥(subdegrees G Ω),
      (commonDivisorGraph (subdegrees G Ω)).connectedComponentMk s ≠
        (commonDivisorGraph (subdegrees G Ω)).connectedComponentMk t →
      (s : ℕ) < (t : ℕ) →
      (stabilizer G α₀).relIndex (arrowKernel G (s : ℕ) α₀) ∣ (t : ℕ) := by
    intro s t hst hlt
    obtain ⟨δ, ε, hw⟩ := t.2
    obtain ⟨γ, hw'⟩ := hw.exists_of_point α₀
    exact relIndex_arrowKernel_dvd_of_isArrow hlt hw'
      (separation_of_connectedComponentMk_ne hst)
  -- `k_s ∣ k_t` for `s < t` in different components (Thm 8.42 (a))
  have hkk : ∀ s t : ↥(subdegrees G Ω),
      (commonDivisorGraph (subdegrees G Ω)).connectedComponentMk s ≠
        (commonDivisorGraph (subdegrees G Ω)).connectedComponentMk t →
      (s : ℕ) < (t : ℕ) →
      (stabilizer G α₀).relIndex (arrowKernel G (s : ℕ) α₀) ∣
        (stabilizer G α₀).relIndex (arrowKernel G (t : ℕ) α₀) := by
    intro s t hst hlt
    obtain ⟨δ, ε, hw⟩ := t.2
    obtain ⟨γ, hw'⟩ := hw.exists_of_point α₀
    have h2 := relIndex_arrowKernel_dvd_relIndex_arrowKernel hlt hw'
      (separation_of_connectedComponentMk_ne hst)
    rwa [relIndex_arrowKernel_eq (t : ℕ) γ α₀] at h2
  -- `k_s > 1` for subdegrees `s ≠ 1`
  have hk1 : ∀ s : ↥(subdegrees G Ω), (s : ℕ) ≠ 1 →
      1 < (stabilizer G α₀).relIndex (arrowKernel G (s : ℕ) α₀) := by
    intro s hs1
    have hpos := subdegrees_pos s
    obtain ⟨δ, ε, hw⟩ := s.2
    obtain ⟨β, hw'⟩ := hw.exists_of_point α₀
    exact one_lt_relIndex_arrowKernel_of_isArrow (by omega) hw'
  -- clause (i)
  have hi : ∀ a b : ↥(subdegrees G Ω),
      (commonDivisorGraph (subdegrees G Ω)).connectedComponentMk a = cA →
      (commonDivisorGraph (subdegrees G Ω)).connectedComponentMk b = cB →
      (a : ℕ) < (b : ℕ) := by
    intro a b ha hb
    have hab' : (commonDivisorGraph (subdegrees G Ω)).connectedComponentMk a ≠
        (commonDivisorGraph (subdegrees G Ω)).connectedComponentMk b := by
      rw [ha, hb]
      exact hAB
    have hvab := hvalne a b hab'
    rcases Nat.lt_or_ge (a : ℕ) (b : ℕ) with h | h
    · exact h
    · exfalso
      have hba : (b : ℕ) < (a : ℕ) := by omega
      have h1 := hkdvd b a hab'.symm hba
      have h3 := hkk b a hab'.symm hba
      have haν : (commonDivisorGraph (subdegrees G Ω)).connectedComponentMk a ≠
          (commonDivisorGraph (subdegrees G Ω)).connectedComponentMk ν := by
        rw [ha, hν]
        exact hAB
      have haltν : (a : ℕ) < (ν : ℕ) :=
        lt_of_le_of_ne (hmax a) (hvalne a ν haν)
      have h4 := hkdvd a ν haν haltν
      have h5 : (stabilizer G α₀).relIndex (arrowKernel G (b : ℕ) α₀) ∣
          Nat.gcd (a : ℕ) (ν : ℕ) :=
        Nat.dvd_gcd h1 (dvd_trans h3 h4)
      have h6 := hk1 b (hB1 b hb)
      have h7 : Nat.gcd (a : ℕ) (ν : ℕ) = 1 :=
        coprime_of_connectedComponentMk_ne haν
      rw [h7] at h5
      have := Nat.dvd_one.mp h5
      omega
  refine ⟨hi, ?_⟩
  -- clause (ii)
  intro u v hu hv huv
  obtain ⟨a, ha⟩ : ∃ a, (commonDivisorGraph
      (subdegrees G Ω)).connectedComponentMk a = cA := Quot.exists_rep cA
  have hau : (a : ℕ) < (u : ℕ) := hi a u ha hu
  have hav : (a : ℕ) < (v : ℕ) := hi a v ha hv
  have hua : (commonDivisorGraph (subdegrees G Ω)).connectedComponentMk a ≠
      (commonDivisorGraph (subdegrees G Ω)).connectedComponentMk u := by
    rw [ha, hu]
    exact hAB
  have hva : (commonDivisorGraph (subdegrees G Ω)).connectedComponentMk a ≠
      (commonDivisorGraph (subdegrees G Ω)).connectedComponentMk v := by
    rw [ha, hv]
    exact hAB
  have h1 := hkdvd a u hua hau
  have h2 := hkdvd a v hva hav
  have h3 := hk1 a (hA1 a ha)
  intro hcop
  have h4 : (stabilizer G α₀).relIndex (arrowKernel G (a : ℕ) α₀) ∣
      Nat.gcd (u : ℕ) (v : ℕ) :=
    Nat.dvd_gcd h1 h2
  have hcop' : Nat.gcd (u : ℕ) (v : ℕ) = 1 := hcop
  rw [hcop'] at h4
  have := Nat.dvd_one.mp h4
  omega

end Theorem843

/-! ### Isaacs Cor 8.44 -/

section Corollary844

open SemidirectProduct

variable (A M : Type*) [Group A] [Group M] [Finite A] [Finite M]
  [MulDistribMulAction A M]

/-- The set of orbit sizes of an action by automorphisms. -/
@[expose] def autOrbitSizes : Set ℕ := {d | ∃ x : M, Set.ncard (orbit A x) = d}

/-- The semidirect product realizing an automorphism action (Isaacs
p. 251: `Γ = G ⋊ A`). -/
private abbrev sdGroup := M ⋊[MulDistribMulAction.toMulAut A M] A

private abbrev sdPoint : Subgroup (sdGroup A M) :=
  (inr : A →* sdGroup A M).range

private abbrev sdSpace := sdGroup A M ⧸ sdPoint A M

private def sdEmbed (x : M) : sdSpace A M :=
  ((inl x : sdGroup A M) : sdSpace A M)

omit [Finite A] [Finite M] in
private lemma sdEmbed_surjective : Function.Surjective (sdEmbed A M) := by
  intro ω
  obtain ⟨γ, rfl⟩ := QuotientGroup.mk_surjective ω
  refine ⟨γ.left, ?_⟩
  have h2 : (inl γ.left * inr γ.right : sdGroup A M) = γ :=
    inl_left_mul_inr_right γ
  calc sdEmbed A M γ.left
      = ((inl γ.left * inr γ.right : sdGroup A M) : sdSpace A M) :=
        (QuotientGroup.mk_mul_of_mem _
          (MonoidHom.mem_range.mpr ⟨γ.right, rfl⟩)).symm
    _ = (γ : sdSpace A M) := by rw [h2]

omit [Finite A] [Finite M] in
private lemma sdEmbed_injective : Function.Injective (sdEmbed A M) := by
  intro x y h
  have h2 := QuotientGroup.eq.mp h
  rw [← map_inv, ← map_mul] at h2
  obtain ⟨b, hb⟩ := MonoidHom.mem_range.mp h2
  have h3 := congrArg SemidirectProduct.left hb
  rw [left_inr, left_inl] at h3
  have h4 : x * 1 = x * (x⁻¹ * y) := congrArg (x * ·) h3
  rwa [mul_one, ← mul_assoc, mul_inv_cancel, one_mul] at h4

omit [Finite A] [Finite M] in
/-- The `A`-orbits on `M` match the suborbits at the trivial coset. -/
private lemma sdEmbed_image_orbit (x : M) :
    sdEmbed A M '' orbit A x =
      orbit (stabilizer (sdGroup A M) ((1 : sdGroup A M) : sdSpace A M))
        (sdEmbed A M x) := by
  have hstab : ∀ γ : sdGroup A M,
      γ ∈ stabilizer (sdGroup A M) ((1 : sdGroup A M) : sdSpace A M) ↔
        γ ∈ sdPoint A M := by
    intro γ
    rw [MulAction.stabilizer_quotient]
  ext ω
  constructor
  · rintro ⟨y, hy, rfl⟩
    rw [MulAction.mem_orbit_iff] at hy ⊢
    obtain ⟨a, rfl⟩ := hy
    refine ⟨⟨inr a, (hstab _).mpr (MonoidHom.mem_range.mpr ⟨a, rfl⟩)⟩, ?_⟩
    have h2 : (⟨inr a, (hstab _).mpr (MonoidHom.mem_range.mpr ⟨a, rfl⟩)⟩ :
          stabilizer (sdGroup A M) ((1 : sdGroup A M) : sdSpace A M)) •
        sdEmbed A M x =
        ((inr a * inl x : sdGroup A M) : sdSpace A M) := rfl
    rw [h2]
    have h3 : (inl (a • x) : sdGroup A M) = inr a * inl x * inr a⁻¹ :=
      inl_aut a x
    rw [sdEmbed, h3, QuotientGroup.mk_mul_of_mem _
      (MonoidHom.mem_range.mpr ⟨a⁻¹, rfl⟩)]
  · rintro ⟨k, hk⟩
    have hk' : k • sdEmbed A M x = ω := hk
    obtain ⟨a, ha⟩ := MonoidHom.mem_range.mp ((hstab _).mp k.2)
    refine ⟨a • x, mem_orbit x a, ?_⟩
    rw [← hk']
    have h2 : k • sdEmbed A M x =
        (((k : sdGroup A M) * inl x : sdGroup A M) : sdSpace A M) := rfl
    rw [h2, ← ha]
    have h4 : (inl (a • x) : sdGroup A M) = inr a * inl x * inr a⁻¹ :=
      inl_aut a x
    rw [sdEmbed, h4, QuotientGroup.mk_mul_of_mem _
      (MonoidHom.mem_range.mpr ⟨a⁻¹, rfl⟩)]

omit [Finite A] [Finite M] in
private lemma autOrbitSizes_eq_subdegrees :
    autOrbitSizes A M = subdegrees (sdGroup A M) (sdSpace A M) := by
  ext d
  constructor
  · rintro ⟨x, hx⟩
    refine ⟨((1 : sdGroup A M) : sdSpace A M), sdEmbed A M x, ?_⟩
    rw [isArrow_iff]
    change Set.ncard (orbit (stabilizer (sdGroup A M)
      ((1 : sdGroup A M) : sdSpace A M)) (sdEmbed A M x)) = d
    rw [← sdEmbed_image_orbit,
      Set.ncard_image_of_injective _ (sdEmbed_injective A M)]
    exact hx
  · rintro ⟨δ, ε, h⟩
    obtain ⟨ε', h'⟩ := h.exists_of_point ((1 : sdGroup A M) : sdSpace A M)
    obtain ⟨x, rfl⟩ := sdEmbed_surjective A M ε'
    refine ⟨x, ?_⟩
    rw [isArrow_iff] at h'
    change Set.ncard (orbit (stabilizer (sdGroup A M)
      ((1 : sdGroup A M) : sdSpace A M)) (sdEmbed A M x)) = d at h'
    rw [← sdEmbed_image_orbit,
      Set.ncard_image_of_injective _ (sdEmbed_injective A M)] at h'
    exact h'

/-- **Isaacs Cor 8.44** (p. 251), first assertion — for finite groups `A`
acting on `M` by automorphisms, the common-divisor graph on the set of
`A`-orbit sizes has at most three connected components (including
`{1}`).  (With `A = M` acting by conjugation this applies to the set of
class sizes of an arbitrary finite group.) -/
theorem card_connectedComponent_commonDivisorGraph_autOrbitSizes_le_three :
    Nat.card
      (commonDivisorGraph (autOrbitSizes A M)).ConnectedComponent ≤ 3 := by
  have : Finite (sdGroup A M) :=
    Finite.of_equiv (M × A)
      ⟨fun p => ⟨p.1, p.2⟩, fun s => (s.left, s.right),
        fun _p => rfl, fun _s => rfl⟩
  rw [autOrbitSizes_eq_subdegrees]
  exact card_connectedComponent_commonDivisorGraph_le_three

/-- **Isaacs Cor 8.44** (p. 251), second assertion — the conclusion of
Thm 8.43 for the orbit sizes of an automorphism action. -/
theorem lt_forall_and_not_coprime_of_max_mem_autOrbitSizes
    {cA cB : (commonDivisorGraph (autOrbitSizes A M)).ConnectedComponent}
    (hAB : cA ≠ cB)
    (hA1 : ∀ t : ↥(autOrbitSizes A M),
      (commonDivisorGraph (autOrbitSizes A M)).connectedComponentMk t = cA →
      (t : ℕ) ≠ 1)
    (hB1 : ∀ t : ↥(autOrbitSizes A M),
      (commonDivisorGraph (autOrbitSizes A M)).connectedComponentMk t = cB →
      (t : ℕ) ≠ 1)
    {ν : ↥(autOrbitSizes A M)}
    (hν : (commonDivisorGraph (autOrbitSizes A M)).connectedComponentMk ν =
      cB)
    (hmax : ∀ d : ↥(autOrbitSizes A M), (d : ℕ) ≤ (ν : ℕ)) :
    (∀ a b : ↥(autOrbitSizes A M),
      (commonDivisorGraph (autOrbitSizes A M)).connectedComponentMk a = cA →
      (commonDivisorGraph (autOrbitSizes A M)).connectedComponentMk b = cB →
      (a : ℕ) < (b : ℕ)) ∧
    (∀ u v : ↥(autOrbitSizes A M),
      (commonDivisorGraph (autOrbitSizes A M)).connectedComponentMk u = cB →
      (commonDivisorGraph (autOrbitSizes A M)).connectedComponentMk v = cB →
      u ≠ v → ¬ Nat.Coprime (u : ℕ) (v : ℕ)) := by
  have : Finite (sdGroup A M) :=
    Finite.of_equiv (M × A)
      ⟨fun p => ⟨p.1, p.2⟩, fun s => (s.left, s.right),
        fun _p => rfl, fun _s => rfl⟩
  revert cA cB hAB hA1 hB1 ν hν hmax
  rw [autOrbitSizes_eq_subdegrees]
  intro cA cB hAB hA1 hB1 ν hν hmax
  exact lt_forall_and_not_coprime_of_max_mem hAB hA1 hB1 hν hmax

end Corollary844

end FiveTransitive.OddOrder.Isaacs.Ch08

end CFSG
