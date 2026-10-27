/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
module

public import Mathlib.GroupTheory.GroupAction.MultipleTransitivity
public import Mathlib.GroupTheory.GroupAction.Quotient
public import Mathlib.GroupTheory.SemidirectProduct

/-!
# Isaacs, Finite Group Theory — Ch. 8: regular normal subgroups (Thm 8.5, Cor 8.6)

Formalizes **Isaacs Thm 8.5** and **Cor 8.6** (pp. 227–228).

* `isPretransitive_subgroup_iff_mul_stabilizer_eq_univ` — **Thm 8.5, first
  assertion**: for `G` transitive on `Ω` with point stabilizer `A`, a subgroup
  `N ≤ G` is transitive iff `N * A = G`.  (Isaacs writes `AN = G` for right
  actions; with mathlib's left actions the natural product order is `N * A`.)
* `injective_smulBase_iff_disjoint_stabilizer`, `surjective_smulBase_iff`,
  `bijective_smulBase_iff` — **Thm 8.5, second assertion**: `N` is regular
  (the orbit map `n ↦ n • α` is bijective) iff it is transitive and
  `N ⊓ A = ⊥`.
* `ofStabilizerToNonidentity` — **Thm 8.5, third assertion**: if `N` is a
  regular normal subgroup, the inverse orbit map is a bijection from
  `Ω − {α}` (as the `SubMulAction.ofStabilizer G α` of `A`) onto the
  nonidentity elements of `N`, equivariant over the conjugation homomorphism
  `A →* MulAut ↥N`.  This is Isaacs's "the conjugation action of `A` on
  `N − {1}` is permutation isomorphic to the action of `A` on `Ω − {α}`".
* `SemidirectProduct.isMultiplyPretransitive_quotient_inrRange` — **Cor 8.6**:
  if a group `A` acts by automorphisms on a group `H` and the action on
  `H − {1}` is `k`-transitive, then `H ⋊ A` acts `(k+1)`-transitively on the
  cosets of `A`.

The `SubMulAction` of nonidentity elements under a `MulDistribMulAction`
(the multiplicative analog of `nonzeroSubMulAction`) is general-purpose and
written mathlib-compatibly for future upstreaming.

Isaacs Lem 8.1 and Lem 8.2 are already in mathlib
(`MulAction.isPretransitive_quotient` + `MulAction.stabilizer_quotient`;
`SubMulAction.ofStabilizer.isMultiplyPretransitive`), and Lem 8.3 is
`Projectivization.specialLinearGroup_is_two_pretransitive`; see
`NonzeroVectors.lean` for Cor 8.4.
-/

public section

namespace CFSG

namespace FiveTransitive.OddOrder.Isaacs.Ch08

open MulAction SubMulAction

open scoped Pointwise

/-! ### The action of a group on the nonidentity elements

A group acting by automorphisms on a group `H` preserves the set of
nonidentity elements.  This is the multiplicative analog of
`nonzeroSubMulAction` (`NonzeroVectors.lean`). -/

section Nonidentity

variable (Γ H : Type*) [Group Γ] [Group H] [MulDistribMulAction Γ H]

/-- The nonidentity elements of a group `H` are invariant under any action of
a group `Γ` on `H` by automorphisms. -/
@[expose] def nonidentitySubMulAction : SubMulAction Γ H where
  carrier := {h | h ≠ 1}
  smul_mem' g _ hh := fun h1 =>
    hh (MulAction.injective g (h1.trans (smul_one g).symm))

instance instMulActionNonidentity : MulAction Γ {h : H // h ≠ 1} :=
  inferInstanceAs <| MulAction Γ (nonidentitySubMulAction Γ H)

variable {Γ H}

@[simp]
lemma nonidentity_smul_coe (g : Γ) (h : {h : H // h ≠ 1}) :
    (g • h : {h : H // h ≠ 1}).1 = g • h.1 :=
  rfl

end Nonidentity

/-! ### Isaacs Thm 8.5: transitive and regular subgroups -/

section RegularSubgroup

variable {G Ω : Type*} [Group G] [MulAction G Ω] {N : Subgroup G} {α : Ω}

/-- The orbit map of a subgroup at a base point.  `N` is transitive iff this
is surjective (`surjective_smulBase_iff`), and *regular* in the sense of
Isaacs Ch. 8 iff it is bijective (`bijective_smulBase_iff`). -/
@[expose] def smulBase (N : Subgroup G) (α : Ω) : N → Ω := fun n => (n : G) • α

@[simp] lemma smulBase_apply (n : N) : smulBase N α n = (n : G) • α := rfl

/-- A subgroup is transitive iff its orbit map at any base point is
surjective. -/
lemma surjective_smulBase_iff (N : Subgroup G) (α : Ω) :
    Function.Surjective (smulBase N α) ↔ IsPretransitive N Ω := by
  rw [isPretransitive_iff_base (G := N) α]
  exact ⟨fun h x => h x, fun h x => h x⟩

/-- The orbit map of a subgroup at `α` is injective iff the subgroup
intersects the stabilizer of `α` trivially. -/
lemma injective_smulBase_iff_disjoint_stabilizer (N : Subgroup G) (α : Ω) :
    Function.Injective (smulBase N α) ↔ N ⊓ stabilizer G α = ⊥ := by
  constructor
  · intro hinj
    rw [eq_bot_iff]
    rintro g ⟨hgN, hgα⟩
    have : smulBase N α ⟨g, hgN⟩ = smulBase N α 1 := by
      simpa [smulBase] using hgα
    simpa [Subtype.ext_iff] using hinj this
  · intro hbot n m hnm
    have : ((m : G)⁻¹ * n) • α = α := by
      rw [mul_smul, inv_smul_eq_iff]
      exact hnm
    have hmem : (m : G)⁻¹ * n ∈ N ⊓ stabilizer G α :=
      ⟨N.mul_mem m⁻¹.2 n.2, this⟩
    rw [hbot, Subgroup.mem_bot, inv_mul_eq_one] at hmem
    exact Subtype.ext hmem.symm

/-- **Isaacs Thm 8.5, first assertion** — if `G` is transitive on `Ω` with
point stabilizer `A = G_α`, a subgroup `N ≤ G` is transitive on `Ω` iff
`N * A = G` as a set product.  (Isaacs states `AN = G`; for mathlib's left
actions the natural order is `N * A`, and the two are equivalent by taking
inverses.) -/
theorem isPretransitive_subgroup_iff_mul_stabilizer_eq_univ
    [IsPretransitive G Ω] (N : Subgroup G) (α : Ω) :
    IsPretransitive N Ω ↔
      (N : Set G) * (stabilizer G α : Set G) = Set.univ := by
  rw [← surjective_smulBase_iff]
  constructor
  · intro h
    ext g
    simp only [Set.mem_univ, iff_true]
    obtain ⟨n, hn⟩ := h (g • α)
    refine ⟨n, n.2, (n : G)⁻¹ * g, ?_, by group⟩
    rw [SetLike.mem_coe, mem_stabilizer_iff, mul_smul, ← hn, smulBase_apply,
      inv_smul_smul]
  · intro h β
    obtain ⟨g, hg⟩ := exists_smul_eq G α β
    have hmem : g ∈ (N : Set G) * (stabilizer G α : Set G) := by
      rw [h]; trivial
    obtain ⟨n, hn, s, hs, rfl⟩ := hmem
    refine ⟨⟨n, hn⟩, ?_⟩
    rw [smulBase_apply, ← hg, mul_smul]
    congr 1
    exact (mem_stabilizer_iff.mp hs).symm

/-- **Isaacs Thm 8.5, second assertion** — for `G` transitive on `Ω`, a
subgroup `N` is *regular* (bijective orbit map) iff it is transitive and
meets the point stabilizer trivially. -/
theorem bijective_smulBase_iff (N : Subgroup G) (α : Ω) :
    Function.Bijective (smulBase N α) ↔
      IsPretransitive N Ω ∧ N ⊓ stabilizer G α = ⊥ := by
  rw [Function.Bijective, and_comm,
    injective_smulBase_iff_disjoint_stabilizer, surjective_smulBase_iff]

/-! ### Isaacs Thm 8.5, third assertion: the conjugation action on a regular
normal subgroup -/

section RegularNormal

variable (hb : Function.Bijective (smulBase N α))

/-- For a regular subgroup `N`, the inverse of the orbit map: the unique
element of `N` carrying the base point `α` to `β`. -/
@[expose] noncomputable def preSmulBase (hb : Function.Bijective (smulBase N α)) (β : Ω) : N :=
  (Equiv.ofBijective _ hb).symm β

@[simp]
lemma smulBase_preSmulBase (β : Ω) : (preSmulBase hb β : G) • α = β :=
  (Equiv.ofBijective _ hb).apply_symm_apply β

lemma preSmulBase_eq_iff {β : Ω} {n : N} : preSmulBase hb β = n ↔ (n : G) • α = β := by
  rw [preSmulBase, Equiv.symm_apply_eq]
  exact eq_comm

/-- **Isaacs Thm 8.5, third assertion** — if `N` is a regular normal subgroup
of `G` acting on `Ω`, then the inverse orbit map is an equivariant bijection
(`ofStabilizerToNonidentity_bijective`) from `Ω − {α}` — as the
`SubMulAction.ofStabilizer` of the point stabilizer `A = G_α` — onto the
nonidentity elements of `N` with `A` acting by conjugation.  In Isaacs's
words: the conjugation action of `A` on `N − {1}` is permutation isomorphic
to the action of `A` on `Ω − {α}`. -/
@[expose] noncomputable def ofStabilizerToNonidentity [N.Normal]
    (hb : Function.Bijective (smulBase N α)) :
    ofStabilizer G α →ₑ[(MulAut.conjNormal (H := N)).comp (stabilizer G α).subtype]
      {n : ↥N // n ≠ 1} where
  toFun β :=
    ⟨preSmulBase hb (β : Ω), by
      intro h1
      apply neq_of_mem_ofStabilizer G α (x := β)
      have := smulBase_preSmulBase hb (β : Ω)
      rw [h1, OneMemClass.coe_one, one_smul] at this
      exact this.symm⟩
  map_smul' a β := by
    apply Subtype.ext
    rw [nonidentity_smul_coe]
    rw [preSmulBase_eq_iff]
    have hβ : (preSmulBase hb (β : Ω) : G) • α = (β : Ω) := smulBase_preSmulBase hb _
    have ha : (a : G)⁻¹ • α = α := by
      rw [inv_smul_eq_iff]
      exact a.2.symm
    change ((a : G) * (preSmulBase hb (β : Ω) : G) * (a : G)⁻¹) • α
      = ((a • β : ofStabilizer G α) : Ω)
    rw [mul_smul, mul_smul, ha, hβ, ← subgroup_smul_def a (β : Ω),
      ← SubMulAction.val_smul]

lemma ofStabilizerToNonidentity_bijective [N.Normal]
    (hb : Function.Bijective (smulBase N α)) :
    Function.Bijective (ofStabilizerToNonidentity hb) := by
  constructor
  · intro β γ h
    have h' : preSmulBase hb (β : Ω) = preSmulBase hb (γ : Ω) :=
      congrArg Subtype.val h
    exact SetLike.coe_eq_coe.mp ((Equiv.ofBijective _ hb).symm.injective h')
  · rintro ⟨n, hn⟩
    have hmem : (n : G) • α ∈ ofStabilizer G α := by
      rw [mem_ofStabilizer_iff]
      intro h
      exact hn (hb.1 (by simpa [smulBase, Subtype.ext_iff] using h))
    refine ⟨⟨(n : G) • α, hmem⟩, Subtype.ext ?_⟩
    change preSmulBase hb ((⟨(n : G) • α, hmem⟩ : ofStabilizer G α) : Ω) = n
    rw [preSmulBase_eq_iff]

end RegularNormal

end RegularSubgroup

/-! ### Isaacs Cor 8.6: multiply transitive semidirect products -/

section SemidirectProduct

open SemidirectProduct

variable (A H : Type*) [Group A] [Group H] [MulDistribMulAction A H]

local notation "G₀" => H ⋊[MulDistribMulAction.toMulAut A H] A

/-- **Isaacs Cor 8.6** — let a group `A` act by automorphisms on a group `H`,
`k`-transitively on the nonidentity elements of `H`.  Then the semidirect
product `H ⋊ A` acts `(k+1)`-transitively on the cosets of `A`. -/
theorem semidirectProduct_isMultiplyPretransitive_quotient_inrRange {k : ℕ}
    (hk : IsMultiplyPretransitive A {h : H // h ≠ 1} k) :
    IsMultiplyPretransitive G₀
      (G₀ ⧸ (inr : A →* G₀).range) (k + 1) := by
  set K : Subgroup G₀ := (inr : A →* G₀).range with hK
  refine (ofStabilizer.isMultiplyPretransitive
    (a := ((1 : G₀) : G₀ ⧸ K))).mpr ?_
  -- transfer `hk` along an equivariant surjection from the nonidentity
  -- elements of `H` onto `(G₀ ⧸ K) − {1}`
  have hstab : ∀ a : A, (inr a : G₀) ∈ stabilizer G₀ ((1 : G₀) : G₀ ⧸ K) := by
    intro a
    rw [mem_stabilizer_iff, MulAction.Quotient.smul_mk, smul_eq_mul, mul_one,
      QuotientGroup.eq]
    exact ⟨a⁻¹, by simp⟩
  let σ : A →* stabilizer G₀ ((1 : G₀) : G₀ ⧸ K) :=
    (inr : A →* G₀).codRestrict _ hstab
  have hmk : ∀ {h : H}, h ≠ 1 →
      ((inl h : G₀) : G₀ ⧸ K) ∈ ofStabilizer G₀ ((1 : G₀) : G₀ ⧸ K) := by
    intro h hh
    rw [mem_ofStabilizer_iff, ne_eq, QuotientGroup.eq]
    rintro ⟨a, ha⟩
    apply hh
    rw [mul_one] at ha
    have ha' : (inl h⁻¹ : G₀) = inr a := by rw [map_inv]; exact ha.symm
    have hleft := congrArg SemidirectProduct.left ha'
    rw [left_inl, left_inr] at hleft
    exact inv_eq_one.mp hleft
  let f : {h : H // h ≠ 1} →ₑ[σ] ofStabilizer G₀ ((1 : G₀) : G₀ ⧸ K) :=
    { toFun h := ⟨((inl h.1 : G₀) : G₀ ⧸ K), hmk h.2⟩
      map_smul' a h := by
        apply Subtype.ext
        change ((inl ((MulDistribMulAction.toMulAut A H) a h.1) : G₀) : G₀ ⧸ K)
          = (inr a : G₀) • ((inl h.1 : G₀) : G₀ ⧸ K)
        rw [inl_aut, MulAction.Quotient.smul_mk, smul_eq_mul, QuotientGroup.eq]
        refine ⟨a, ?_⟩
        rw [map_inv]
        group }
  have hf : Function.Surjective f := by
    rintro ⟨β, hβ⟩
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective β
    have hg1 : g.left ≠ 1 := by
      intro h1
      rw [mem_ofStabilizer_iff] at hβ
      apply hβ
      have hg : (g : G₀) = inr g.right := by
        conv_lhs => rw [← inl_left_mul_inr_right g]
        rw [h1, map_one, one_mul]
      rw [hg, QuotientGroup.eq]
      exact ⟨g.right⁻¹, by rw [map_inv, mul_one]⟩
    refine ⟨⟨g.left, hg1⟩, Subtype.ext ?_⟩
    change ((inl g.left : G₀) : G₀ ⧸ K) = ((g : G₀) : G₀ ⧸ K)
    rw [QuotientGroup.eq]
    refine ⟨g.right, ?_⟩
    have hcalc : (inl g.left : G₀)⁻¹ * (inl g.left * inr g.right) = inr g.right := by
      group
    rw [inl_left_mul_inr_right g] at hcalc
    exact hcalc.symm
  exact IsPretransitive.of_embedding (f := f) hf

/-! Supporting API for Cor 8.6: the coset space of `A` in `H ⋊ A` is in
bijection with `H`, and the coset action is faithful when the action of `A`
on `H` is.  (Isaacs uses these in Cor 8.7 to conclude that `V ⋊ GL(n,2)` is
a *permutation group* of degree `2^n`.) -/

lemma semidirectProduct_mem_inrRange_iff {x : G₀} :
    x ∈ (inr : A →* G₀).range ↔ x.left = 1 := by
  constructor
  · rintro ⟨a, rfl⟩
    exact left_inr a
  · intro h
    refine ⟨x.right, ?_⟩
    ext
    · rw [left_inr, h]
    · rw [right_inr]

lemma semidirectProduct_inr_mul_inl (a : A) (h : H) :
    (inr a * inl h : G₀) = inl (MulDistribMulAction.toMulAut A H a h) * inr a := by
  rw [inl_aut, map_inv]
  group

/-- The coset space of `A` in `H ⋊ A` is in bijection with `H`, via
`h ↦ ⟦inl h⟧`.  (In Isaacs's terms: the degree of the coset action of
`H ⋊ A` is `|H|`.) -/
@[expose] noncomputable def semidirectProductQuotientInrEquiv :
    H ≃ G₀ ⧸ (inr : A →* G₀).range := by
  refine Equiv.ofBijective (fun h => ((inl h : G₀) : G₀ ⧸ (inr : A →* G₀).range))
    ⟨fun h h' hhh' => ?_, fun β => ?_⟩
  · rw [QuotientGroup.eq, ← map_inv, ← map_mul,
      semidirectProduct_mem_inrRange_iff, left_inl] at hhh'
    exact inv_mul_eq_one.mp hhh'
  · obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective β
    refine ⟨g.left, ?_⟩
    conv_rhs => rw [← inl_left_mul_inr_right g]
    rw [QuotientGroup.mk_mul_of_mem _ (MonoidHom.mem_range.mpr ⟨g.right, rfl⟩)]

@[simp]
lemma semidirectProductQuotientInrEquiv_apply (h : H) :
    semidirectProductQuotientInrEquiv A H h
      = ((inl h : G₀) : G₀ ⧸ (inr : A →* G₀).range) :=
  rfl

/-- If the action of `A` on `H` is faithful, then the action of `H ⋊ A` on
the coset space of `A` is faithful.  (Kernel argument of Isaacs Cor 8.7: the
kernel `K` lies in `A` and is normal, so `[H, K] ≤ H ∩ K = 1`, forcing `K`
to act trivially on `H`.) -/
theorem semidirectProduct_quotient_inrRange_faithfulSMul [FaithfulSMul A H] :
    FaithfulSMul G₀ (G₀ ⧸ (inr : A →* G₀).range) where
  eq_of_smul_eq_smul {g₁ g₂} hfix := by
    set K : Subgroup G₀ := (inr : A →* G₀).range with hK
    -- reduce to: `g := g₂⁻¹ * g₁` acts trivially, hence is `1`
    suffices htriv : ∀ g : G₀, (∀ x : G₀ ⧸ K, g • x = x) → g = 1 by
      have := htriv (g₂⁻¹ * g₁) fun x => by
        rw [mul_smul, hfix x, inv_smul_smul]
      rwa [inv_mul_eq_one, eq_comm] at this
    intro g hg
    -- `g` stabilizes the base coset, so `g = inr a`
    have hmem : g ∈ K := by
      rw [hK, ← MulAction.stabilizer_quotient ((inr : A →* G₀).range)]
      exact hg ((1 : G₀) : G₀ ⧸ K)
    obtain ⟨a, rfl⟩ := hmem
    -- `g` fixes every `⟦inl h⟧`, so `a` fixes every `h`
    have ha : ∀ h : H, a • h = h := by
      intro h
      have := hg ((inl h : G₀) : G₀ ⧸ K)
      rw [MulAction.Quotient.smul_mk, smul_eq_mul,
        semidirectProduct_inr_mul_inl,
        QuotientGroup.mk_mul_of_mem _ (MonoidHom.mem_range.mpr ⟨a, rfl⟩)]
        at this
      exact (semidirectProductQuotientInrEquiv A H).injective this
    rw [← map_one (inr : A →* G₀)]
    congr 1
    exact FaithfulSMul.eq_of_smul_eq_smul fun h => by rw [ha h, one_smul]

lemma semidirectProduct_natCard_quotient_inrRange :
    Nat.card (G₀ ⧸ (inr : A →* G₀).range) = Nat.card H :=
  (Nat.card_congr (semidirectProductQuotientInrEquiv A H)).symm

end SemidirectProduct

end FiveTransitive.OddOrder.Isaacs.Ch08

end CFSG
