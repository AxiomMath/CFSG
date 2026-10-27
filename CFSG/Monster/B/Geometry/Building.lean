module

public import CFSG.LieType.Chevalley.C2E6BruhatBuilding
public import CFSG.Monster.B.Geometry.Coxeter

public section

namespace CFSG.Monster.B.Geometry

open CoxeterSystem CFSG.LieType.Chevalley.CosetBuilding

variable {ι : Type*} {M : CoxeterMatrix ι} {W : Type*} [Group W] (cs : CoxeterSystem M W)
variable {C : Type*} (δ : C → C → W)

@[expose] def galleryEnd : C → List (ι × C) → C
  | x, [] => x
  | _, p :: γ => galleryEnd p.2 γ

@[expose] def galleryType (γ : List (ι × C)) : List ι := γ.map Prod.fst

@[expose] def IsStrictGallery : C → List (ι × C) → Prop
  | _, [] => True
  | x, p :: γ => δ x p.2 = cs.simple p.1 ∧ IsStrictGallery p.2 γ

@[expose] def IsReducedGallery (x : C) (γ : List (ι × C)) : Prop :=
  IsStrictGallery cs δ x γ ∧ cs.IsReduced (galleryType γ)

abbrev panel (i : ι) (x : C) : Set C := residue cs δ {i} x

@[expose] def IsThick : Prop := ∀ (i : ι) (x : C), 3 ≤ (panel cs δ i x).encard

@[expose] def coxeterDistance (u v : W) : W := u⁻¹ * v

@[expose] def IsApartmentMap (a : W → C) : Prop := ∀ u v, δ (a u) (a v) = u⁻¹ * v

@[expose] def IsApartment (A : Set C) : Prop :=
  ∃ a : W → C, Function.Injective a ∧ Set.range a = A ∧ IsApartmentMap δ a

@[expose] def IsOpposite (x y : C) : Prop := δ x y = longest cs Set.univ

@[expose] def IsProjection (R : Set C) (z p : C) : Prop :=
  p ∈ R ∧ ∀ q ∈ R, q ≠ p → cs.length (δ z p) < cs.length (δ z q)

@[expose] def foundation (k : ℕ) (x : C) : Set C :=
  ⋃ J : Set ι, ⋃ (_ : J.encard ≤ k), residue cs δ J x

@[expose] def residueFoundation (J : Set ι) (x : C) : Set C :=
  ⋃ I : Set ι, ⋃ (_ : I ⊆ J ∧ I.encard ≤ 2), residue cs δ I x

variable {C' : Type*} (δ' : C' → C' → W)

@[expose] def IsWeylIsometry (X : Set C) (X' : Set C') (f : C → C') : Prop :=
  Set.BijOn f X X' ∧ ∀ x ∈ X, ∀ y ∈ X, δ' (f x) (f y) = δ x y

@[expose] def IsTypeIso (X : Set C) (X' : Set C') (f : C → C') : Prop :=
  Set.BijOn f X X' ∧ ∀ x ∈ X, ∀ y ∈ X, ∀ i, δ' (f x) (f y) = cs.simple i ↔ δ x y = cs.simple i

@[expose] def typeAut : Subgroup (Equiv.Perm C) where
  carrier := {g | ∀ x y i, δ (g x) (g y) = cs.simple i ↔ δ x y = cs.simple i}
  mul_mem' {g h} hg hh x y i := (hg (h x) (h y) i).trans (hh x y i)
  one_mem' _ _ _ := Iff.rfl
  inv_mem' {g} hg x y i := by
    have := hg (g⁻¹ x) (g⁻¹ y) i
    simp only [← Equiv.Perm.mul_apply, mul_inv_cancel, Equiv.Perm.one_apply] at this
    exact this.symm

theorem mem_typeAut {g : Equiv.Perm C} :
    g ∈ typeAut cs δ ↔ ∀ x y i, δ (g x) (g y) = cs.simple i ↔ δ x y = cs.simple i :=
  Iff.rfl

@[expose] def Rig₂ : Prop :=
  ∀ (i j : ι), i ≠ j → ∀ (a b : C), b ∈ residue cs δ {i, j} a → δ a b = longest cs {i, j} →
    ∀ g : C → C, IsTypeIso cs δ δ (residue cs δ {i, j} a) (residue cs δ {i, j} a) g →
      g b = b → (∀ x ∈ panel cs δ i a ∪ panel cs δ j a, g x = x) →
        ∀ x ∈ residue cs δ {i, j} a, g x = x

@[expose] def Ext₃ : Prop :=
  ∀ (J : Set ι), J.ncard = 3 → ∀ (a b : C) (a' b' : C'),
    b ∈ residue cs δ J a → b' ∈ residue cs δ' J a' →
      δ a b = longest cs J → δ' a' b' = longest cs J →
        ∀ f : C → C', IsWeylIsometry δ δ' (residueFoundation cs δ J a ∪ {b})
            (residueFoundation cs δ' J a' ∪ {b'}) f → f a = a' → f b = b' →
          (∃ F : C → C', IsTypeIso cs δ δ' (residue cs δ J a) (residue cs δ' J a') F ∧
              IsWeylIsometry δ δ' (residue cs δ J a) (residue cs δ' J a') F ∧
              Set.EqOn F f (residueFoundation cs δ J a ∪ {b})) ∧
            ∀ F₁ F₂ : C → C',
              IsTypeIso cs δ δ' (residue cs δ J a) (residue cs δ' J a') F₁ →
              IsTypeIso cs δ δ' (residue cs δ J a) (residue cs δ' J a') F₂ →
              Set.EqOn F₁ f (residueFoundation cs δ J a ∪ {b}) →
              Set.EqOn F₂ f (residueFoundation cs δ J a ∪ {b}) →
              Set.EqOn F₁ F₂ (residue cs δ J a)

variable {cs δ}

@[simp] theorem galleryEnd_nil (x : C) : galleryEnd x ([] : List (ι × C)) = x := rfl

@[simp] theorem galleryEnd_cons (x : C) (p : ι × C) (γ : List (ι × C)) :
    galleryEnd x (p :: γ) = galleryEnd p.2 γ := rfl

theorem galleryEnd_append (x : C) (γ η : List (ι × C)) :
    galleryEnd x (γ ++ η) = galleryEnd (galleryEnd x γ) η := by
  induction γ generalizing x with
  | nil => rfl
  | cons p γ ih => exact ih p.2

@[simp] theorem galleryEnd_concat (x : C) (γ : List (ι × C)) (p : ι × C) :
    galleryEnd x (γ ++ [p]) = p.2 := by
  rw [galleryEnd_append]
  rfl

@[simp] theorem galleryType_nil : galleryType ([] : List (ι × C)) = [] := rfl

@[simp] theorem galleryType_cons (p : ι × C) (γ : List (ι × C)) :
    galleryType (p :: γ) = p.1 :: galleryType γ := rfl

@[simp] theorem galleryType_append (γ η : List (ι × C)) :
    galleryType (γ ++ η) = galleryType γ ++ galleryType η := List.map_append ..

@[simp] theorem length_galleryType (γ : List (ι × C)) : (galleryType γ).length = γ.length :=
  List.length_map ..

@[simp] theorem isStrictGallery_nil (x : C) : IsStrictGallery cs δ x [] := trivial

@[simp] theorem isStrictGallery_cons (x : C) (p : ι × C) (γ : List (ι × C)) :
    IsStrictGallery cs δ x (p :: γ) ↔ δ x p.2 = cs.simple p.1 ∧ IsStrictGallery cs δ p.2 γ :=
  Iff.rfl

theorem isStrictGallery_append (x : C) (γ η : List (ι × C)) :
    IsStrictGallery cs δ x (γ ++ η) ↔
      IsStrictGallery cs δ x γ ∧ IsStrictGallery cs δ (galleryEnd x γ) η := by
  induction γ generalizing x with
  | nil => simp
  | cons p γ ih =>
    simp only [List.cons_append, isStrictGallery_cons, ih, galleryEnd_cons, and_assoc]

theorem isStrictGallery_concat (x : C) (γ : List (ι × C)) (p : ι × C) :
    IsStrictGallery cs δ x (γ ++ [p]) ↔
      IsStrictGallery cs δ x γ ∧ δ (galleryEnd x γ) p.2 = cs.simple p.1 := by
  rw [isStrictGallery_append]
  simp

@[expose] def galleryReverse : C → List (ι × C) → List (ι × C)
  | _, [] => []
  | x, p :: γ => galleryReverse p.2 γ ++ [(p.1, x)]

@[simp] theorem galleryReverse_nil (x : C) : galleryReverse x ([] : List (ι × C)) = [] := rfl

@[simp] theorem galleryReverse_cons (x : C) (p : ι × C) (γ : List (ι × C)) :
    galleryReverse x (p :: γ) = galleryReverse p.2 γ ++ [(p.1, x)] := rfl

@[simp] theorem galleryType_galleryReverse (x : C) (γ : List (ι × C)) :
    galleryType (galleryReverse x γ) = (galleryType γ).reverse := by
  induction γ generalizing x with
  | nil => rfl
  | cons p γ ih => simp [ih]

@[simp] theorem length_galleryReverse (x : C) (γ : List (ι × C)) :
    (galleryReverse x γ).length = γ.length := by
  rw [← length_galleryType, galleryType_galleryReverse, List.length_reverse, length_galleryType]

@[simp] theorem galleryEnd_galleryReverse (x : C) (γ : List (ι × C)) :
    galleryEnd (galleryEnd x γ) (galleryReverse x γ) = x := by
  induction γ generalizing x with
  | nil => rfl
  | cons p γ _ => simp

end CFSG.Monster.B.Geometry

namespace CFSG.LieType.Chevalley.CosetBuilding.IsWeylDistanceBuilding

open CFSG.Monster.B.Geometry

variable {ι : Type*} {M : CoxeterMatrix ι} {W : Type*} [Group W] {cs : CoxeterSystem M W}
variable {C : Type*} {δ : C → C → W} (hδ : IsWeylDistanceBuilding cs δ)
include hδ

theorem symm_of_eq_simple {x y : C} {i : ι} (h : δ x y = cs.simple i) : δ y x = cs.simple i := by
  obtain ⟨z, hyz, hxz⟩ := hδ.exists_simple x y i
  rw [h, cs.simple_mul_simple_self, hδ.eq_one_iff] at hxz
  rwa [← hxz] at hyz

theorem eq_simple_comm {x y : C} {i : ι} : δ x y = cs.simple i ↔ δ y x = cs.simple i :=
  ⟨hδ.symm_of_eq_simple, hδ.symm_of_eq_simple⟩

theorem ne_of_eq_simple {x y : C} {i : ι} (h : δ x y = cs.simple i) : x ≠ y := by
  rintro rfl
  have h1 := (hδ.eq_one_iff x x).mpr rfl
  rw [h1] at h
  exact CoxeterSystem.simple_ne_one cs i h.symm

theorem eq_one_self (x : C) : δ x x = 1 := (hδ.eq_one_iff x x).mpr rfl

end CFSG.LieType.Chevalley.CosetBuilding.IsWeylDistanceBuilding

namespace CFSG.Monster.B.Geometry

open CoxeterSystem CFSG.LieType.Chevalley.CosetBuilding

variable {ι : Type*} {M : CoxeterMatrix ι} {W : Type*} [Group W] {cs : CoxeterSystem M W}
variable {C : Type*} {δ : C → C → W}

theorem IsStrictGallery.reverse (hδ : IsWeylDistanceBuilding cs δ) {x : C} {γ : List (ι × C)}
    (hγ : IsStrictGallery cs δ x γ) :
    IsStrictGallery cs δ (galleryEnd x γ) (galleryReverse x γ) := by
  induction γ generalizing x with
  | nil => trivial
  | cons p γ ih =>
    obtain ⟨h1, h2⟩ := hγ
    simp only [galleryEnd_cons, galleryReverse_cons]
    rw [isStrictGallery_concat]
    refine ⟨ih h2, ?_⟩
    rw [galleryEnd_galleryReverse]
    exact hδ.symm_of_eq_simple h1

theorem mem_residue_iff {J : Set ι} {x y : C} :
    y ∈ residue cs δ J x ↔
      ∃ γ : List (ι × C), IsStrictGallery cs δ x γ ∧ (∀ i ∈ galleryType γ, i ∈ J) ∧
        galleryEnd x γ = y := by
  constructor
  · intro h
    induction h with
    | refl => exact ⟨[], trivial, by simp, rfl⟩
    | @tail b c _ hbc ih =>
      obtain ⟨γ, hγ, hJ, rfl⟩ := ih
      obtain ⟨i, hi, hδi⟩ := hbc
      refine ⟨γ ++ [(i, c)], (isStrictGallery_concat _ _ _).mpr ⟨hγ, hδi⟩, ?_, by simp⟩
      intro k hk
      simp only [galleryType_append, List.mem_append] at hk
      rcases hk with hk | hk
      · exact hJ k hk
      · simp only [galleryType_cons, galleryType_nil, List.mem_singleton] at hk
        exact hk ▸ hi
  · rintro ⟨γ, hγ, hJ, rfl⟩
    induction γ generalizing x with
    | nil => exact Relation.ReflTransGen.refl
    | cons p γ ih =>
      obtain ⟨h1, h2⟩ := hγ
      exact Relation.ReflTransGen.head ⟨p.1, hJ p.1 (by simp), h1⟩
        (ih h2 fun k hk => hJ k (by simp [hk]))

theorem self_mem_residue (J : Set ι) (x : C) : x ∈ residue cs δ J x :=
  Relation.ReflTransGen.refl

theorem residue_mono {J K : Set ι} (h : J ⊆ K) (x : C) :
    residue cs δ J x ⊆ residue cs δ K x := by
  intro y hy
  induction hy with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hbc ih =>
    obtain ⟨i, hi, he⟩ := hbc
    exact ih.tail ⟨i, h hi, he⟩

theorem mem_residue_symm (hδ : IsWeylDistanceBuilding cs δ) {J : Set ι} {x y : C}
    (h : y ∈ residue cs δ J x) : x ∈ residue cs δ J y := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | @tail b c _ hbc ih =>
    obtain ⟨i, hi, he⟩ := hbc
    exact Relation.ReflTransGen.head ⟨i, hi, hδ.symm_of_eq_simple he⟩ ih

theorem mem_residue_trans {J : Set ι} {x y z : C} (hxy : y ∈ residue cs δ J x)
    (hyz : z ∈ residue cs δ J y) : z ∈ residue cs δ J x :=
  Relation.ReflTransGen.trans hxy hyz

theorem residue_eq_of_mem (hδ : IsWeylDistanceBuilding cs δ) {J : Set ι} {x y : C}
    (h : y ∈ residue cs δ J x) : residue cs δ J y = residue cs δ J x := by
  ext z
  exact ⟨fun hz => mem_residue_trans h hz,
    fun hz => mem_residue_trans (mem_residue_symm hδ h) hz⟩

theorem IsStrictGallery.mem_parabolic (hδ : IsWeylDistanceBuilding cs δ) {J : Set ι} {x : C}
    {γ : List (ι × C)} (hγ : IsStrictGallery cs δ x γ) (hJ : ∀ i ∈ galleryType γ, i ∈ J) :
    δ x (galleryEnd x γ) ∈ cs.parabolic J := by
  induction γ using List.reverseRecOn with
  | nil => simp [hδ.eq_one_self]
  | append_singleton γ p ih =>
    rw [isStrictGallery_concat] at hγ
    have hJ' : ∀ i ∈ galleryType γ, i ∈ J := fun i hi => hJ i (by simp [hi])
    have hp : p.1 ∈ J := hJ p.1 (by simp)
    have h := ih hγ.1 hJ'
    rcases (hδ.mul_simple x (galleryEnd x γ) p.2 p.1 hγ.2).1 with he | he <;>
      rw [galleryEnd_concat, he]
    · exact h
    · exact mul_mem h (cs.simple_mem_parabolic hp)

theorem mem_parabolic_of_mem_residue (hδ : IsWeylDistanceBuilding cs δ) {J : Set ι}
    {x y z : C} (hy : y ∈ residue cs δ J x) (hz : z ∈ residue cs δ J x) :
    δ y z ∈ cs.parabolic J := by
  have hz' : z ∈ residue cs δ J y := by rwa [residue_eq_of_mem hδ hy]
  obtain ⟨γ, hγ, hJ, rfl⟩ := mem_residue_iff.mp hz'
  exact hγ.mem_parabolic hδ hJ

variable (cs) in
theorem isWeylDistanceBuilding_coxeter : IsWeylDistanceBuilding cs (coxeterDistance (W := W)) where
  nonempty := ⟨1⟩
  eq_one_iff u v := by simp [coxeterDistance, inv_mul_eq_one]
  mul_simple u v z i h := by
    have hz : z = v * cs.simple i := by
      simp only [coxeterDistance] at h
      rw [← h, mul_inv_cancel_left]
    subst hz
    exact ⟨Or.inr (by simp [coxeterDistance, mul_assoc]), fun _ => by
      simp [coxeterDistance, mul_assoc]⟩
  exists_simple u v i := ⟨v * cs.simple i, by simp [coxeterDistance], by
    simp [coxeterDistance, mul_assoc]⟩

end CFSG.Monster.B.Geometry
