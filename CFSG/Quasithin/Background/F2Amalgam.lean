module

public import Mathlib.GroupTheory.PresentedGroup
public import Mathlib.Order.ConditionallyCompleteLattice.Basic

public section

namespace CFSG.Quasithin

universe u v w w'

structure Amalgam (D : Type u) [Preorder D] where
  X : D → Type v
  [grp : ∀ d, Group (X d)]
  map : ∀ {d e : D}, d ≤ e → X d →* X e
  map_self : ∀ (d : D) (x : X d), map (le_refl d) x = x
  map_comp : ∀ {d e f : D} (h₁ : d ≤ e) (h₂ : e ≤ f) (x : X d),
    map (h₁.trans h₂) x = map h₂ (map h₁ x)

attribute [instance] Amalgam.grp

namespace Amalgam

variable {D : Type u} [Preorder D]

section OfSubgroups

variable {Y : Type w} [Group Y]

abbrev ofSubgroups (Yd : D → Subgroup Y) (hY : Monotone Yd) : Amalgam.{u, w} D where
  X d := ↥(Yd d)
  map h := Subgroup.inclusion (hY h)
  map_self _ _ := rfl
  map_comp _ _ _ := rfl

@[simp] theorem ofSubgroups_map_coe (Yd : D → Subgroup Y) (hY : Monotone Yd) {d e : D} (h : d ≤ e)
    (x : Yd d) : ((ofSubgroups Yd hY).map h x).1 = x.1 := rfl

end OfSubgroups

structure Iso (α : Amalgam.{u, v} D) (β : Amalgam.{u, w} D) where
  toEquiv : ∀ d, α.X d ≃* β.X d
  comm : ∀ {d e : D} (h : d ≤ e) (x : α.X d), β.map h (toEquiv d x) = toEquiv e (α.map h x)

@[expose] def autSubgroup (α : Amalgam.{u, v} D) : Subgroup (∀ d, MulAut (α.X d)) where
  carrier := {a | ∀ {d e : D} (h : d ≤ e) (x : α.X d), α.map h (a d x) = a e (α.map h x)}
  one_mem' := fun _ _ => rfl
  mul_mem' := by
    intro a b ha hb d e h x
    rw [Pi.mul_apply, Pi.mul_apply, MulAut.mul_apply, MulAut.mul_apply, ha h, hb h]
  inv_mem' := by
    intro a ha d e h x
    have hx := ha h (((a d)⁻¹ : MulAut (α.X d)) x)
    rw [Pi.inv_apply, Pi.inv_apply]
    have h2 : α.map h x = a e (α.map h ((a d)⁻¹ x)) := by
      rw [← hx]; simp
    rw [h2]
    simp

abbrev Aut (α : Amalgam.{u, v} D) : Type _ := ↥(autSubgroup α)

variable (α : Amalgam.{u, v} D)

namespace Aut

variable {α}

theorem comm (a : Aut α) {d e : D} (h : d ≤ e) (x : α.X d) :
    α.map h (a.1 d x) = a.1 e (α.map h x) := a.2 h x

@[simp] theorem one_apply (d : D) (x : α.X d) : (1 : Aut α).1 d x = x := rfl

@[simp] theorem mul_apply (a b : Aut α) (d : D) (x : α.X d) :
    (a * b).1 d x = a.1 d (b.1 d x) := rfl

theorem inv_apply (a : Aut α) (d : D) (x : α.X d) : (a⁻¹).1 d x = (a.1 d).symm x := rfl

@[simp] theorem apply_inv_apply (a : Aut α) (d : D) (x : α.X d) :
    a.1 d ((a⁻¹).1 d x) = x := by
  rw [inv_apply]; exact (a.1 d).apply_symm_apply x

@[simp] theorem inv_apply_apply (a : Aut α) (d : D) (x : α.X d) :
    (a⁻¹).1 d (a.1 d x) = x := by
  rw [inv_apply]; exact (a.1 d).symm_apply_apply x

end Aut

structure Completion (α : Amalgam.{u, v} D) (G : Type w) [Group G] where
  toHom : ∀ d, α.X d →* G
  comm : ∀ {d e : D} (h : d ≤ e) (x : α.X d), toHom e (α.map h x) = toHom d x
  gen : ⨆ d, (toHom d).range = ⊤

@[expose] def Completion.IsFaithful {α : Amalgam.{u, v} D} {G : Type w} [Group G] (μ : Completion α G) :
    Prop :=
  ∀ d, Function.Injective (μ.toHom d)

@[expose] def rels : Set (FreeGroup (Σ d, α.X d)) :=
  {w | ∃ d, ∃ x y : α.X d,
    w = FreeGroup.of ⟨d, x⟩ * FreeGroup.of ⟨d, y⟩ * (FreeGroup.of ⟨d, x * y⟩)⁻¹} ∪
  {w | ∃ d e, ∃ h : d ≤ e, ∃ x : α.X d,
    w = FreeGroup.of ⟨e, α.map h x⟩ * (FreeGroup.of ⟨d, x⟩)⁻¹}

abbrev gp : Type (max u v) := PresentedGroup (rels α)

variable {α}

theorem mk_rel_eq_one {r : FreeGroup (Σ d, α.X d)} (hr : r ∈ rels α) :
    (QuotientGroup.mk r : PresentedGroup (rels α)) = 1 :=
  (QuotientGroup.eq_one_iff r).mpr (Subgroup.subset_normalClosure hr)

theorem of_mul_of (d : D) (x y : α.X d) :
    (PresentedGroup.of ⟨d, x⟩ : PresentedGroup (rels α)) * PresentedGroup.of ⟨d, y⟩ =
      PresentedGroup.of ⟨d, x * y⟩ := by
  have h := mk_rel_eq_one (α := α) (Or.inl ⟨d, x, y, rfl⟩)
  rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv, mul_inv_eq_one] at h
  exact h

theorem of_map (d e : D) (h : d ≤ e) (x : α.X d) :
    (PresentedGroup.of ⟨e, α.map h x⟩ : PresentedGroup (rels α)) = PresentedGroup.of ⟨d, x⟩ := by
  have h' := mk_rel_eq_one (α := α) (Or.inr ⟨d, e, h, x, rfl⟩)
  rw [QuotientGroup.mk_mul, QuotientGroup.mk_inv, mul_inv_eq_one] at h'
  exact h'

variable (α) in
@[expose] def ξ (d : D) : α.X d →* gp α where
  toFun x := PresentedGroup.of ⟨d, x⟩
  map_one' := by
    have h := of_mul_of (α := α) d 1 1
    rw [mul_one] at h
    exact mul_eq_left.mp h
  map_mul' x y := (of_mul_of d x y).symm

theorem ξ_apply (d : D) (x : α.X d) :
    ξ α d x = (PresentedGroup.of ⟨d, x⟩ : PresentedGroup (rels α)) := rfl

theorem ξ_map {d e : D} (h : d ≤ e) (x : α.X d) : ξ α e (α.map h x) = ξ α d x := of_map d e h x

theorem iSup_range_ξ : ⨆ d, (ξ α d).range = ⊤ := by
  rw [eq_top_iff, ← PresentedGroup.closure_range_of (rels α), Subgroup.closure_le]
  rintro _ ⟨⟨d, x⟩, rfl⟩
  exact (le_iSup (fun d => (ξ α d).range) d) ⟨x, rfl⟩

variable (α) in
@[expose] def univ : Completion α (gp α) where
  toHom := ξ α
  comm h x := ξ_map h x
  gen := iSup_range_ξ

variable {G : Type w} [Group G]

noncomputable def lift (μ : ∀ d, α.X d →* G)
    (hμ : ∀ {d e : D} (h : d ≤ e) (x : α.X d), μ e (α.map h x) = μ d x) : gp α →* G :=
  PresentedGroup.toGroup (f := fun g : Σ d, α.X d => μ g.1 g.2) (by
    rintro r (⟨d, x, y, rfl⟩ | ⟨d, e, h, x, rfl⟩)
    · simp
    · simp [hμ h x])

@[simp] theorem lift_ξ (μ : ∀ d, α.X d →* G)
    (hμ : ∀ {d e : D} (h : d ≤ e) (x : α.X d), μ e (α.map h x) = μ d x) (d : D) (x : α.X d) :
    lift μ hμ (ξ α d x) = μ d x := by
  unfold lift
  rw [ξ_apply]
  exact PresentedGroup.toGroup.of _

theorem hom_ext {f g : gp α →* G} (h : ∀ d (x : α.X d), f (ξ α d x) = g (ξ α d x)) : f = g := by
  refine PresentedGroup.ext fun ⟨d, x⟩ => ?_
  exact h d x

theorem lift_unique (μ : ∀ d, α.X d →* G)
    (hμ : ∀ {d e : D} (h : d ≤ e) (x : α.X d), μ e (α.map h x) = μ d x) (ψ : gp α →* G)
    (hψ : ∀ d (x : α.X d), ψ (ξ α d x) = μ d x) : ψ = lift μ hμ :=
  hom_ext fun d x => by rw [hψ, lift_ξ]

end Amalgam

end CFSG.Quasithin
