module

public import CFSG.Monster.B.Geometry.Gallery

public section

namespace CFSG.Monster.B.Geometry

structure ChamberSystem (I C : Type*) where
  adj : I → C → C → Prop
  equivalence : ∀ i, Equivalence (adj i)

namespace ChamberSystem

variable {I C D E : Type*}

theorem galleryReverse_append (x : C) (γ η : List (I × C)) :
    galleryReverse x (γ ++ η) = galleryReverse (galleryEnd x γ) η ++ galleryReverse x γ := by
  induction γ generalizing x with
  | nil => simp
  | cons p γ ih => simp [ih]

@[simp] theorem galleryReverse_galleryReverse (x : C) (γ : List (I × C)) :
    galleryReverse (galleryEnd x γ) (galleryReverse x γ) = γ := by
  induction γ generalizing x with
  | nil => rfl
  | cons p γ ih =>
    rw [galleryEnd_cons, galleryReverse_cons, galleryReverse_append, galleryEnd_galleryReverse,
      ih]
    rfl

@[simp] theorem galleryMap_nil (f : C → D) : galleryMap f ([] : List (I × C)) = [] := rfl

@[simp] theorem galleryMap_cons (f : C → D) (p : I × C) (γ : List (I × C)) :
    galleryMap f (p :: γ) = (p.1, f p.2) :: galleryMap f γ := rfl

@[simp] theorem galleryMap_append (f : C → D) (γ η : List (I × C)) :
    galleryMap f (γ ++ η) = galleryMap f γ ++ galleryMap f η :=
  List.map_append ..

@[simp] theorem length_galleryMap (f : C → D) (γ : List (I × C)) :
    (galleryMap f γ).length = γ.length :=
  List.length_map ..

theorem galleryMap_galleryMap (f : C → D) (g : D → E) (γ : List (I × C)) :
    galleryMap g (galleryMap f γ) = galleryMap (g ∘ f) γ := by
  simp [galleryMap, Function.comp_def]

@[simp] theorem galleryMap_id (γ : List (I × C)) : galleryMap id γ = γ := by
  simp [galleryMap]

theorem galleryMap_galleryReverse (f : C → D) (x : C) (γ : List (I × C)) :
    galleryMap f (galleryReverse x γ) = galleryReverse (f x) (galleryMap f γ) := by
  induction γ generalizing x with
  | nil => rfl
  | cons p γ ih => simp [ih]

theorem galleryEnd_galleryMap' (f : C → D) {x : C} {y : D} (h : f x = y) (γ : List (I × C)) :
    galleryEnd y (galleryMap f γ) = f (galleryEnd x γ) := by
  rw [← h, galleryEnd_galleryMap]

variable (X : ChamberSystem I C)

theorem adj_refl (i : I) (x : C) : X.adj i x x := (X.equivalence i).refl x

variable {X} in
theorem adj_symm {i : I} {x y : C} (h : X.adj i x y) : X.adj i y x := (X.equivalence i).symm h

variable {X} in
theorem adj_trans {i : I} {x y z : C} (h : X.adj i x y) (h' : X.adj i y z) : X.adj i x z :=
  (X.equivalence i).trans h h'

@[expose] def IsGallery : C → List (I × C) → Prop
  | _, [] => True
  | x, p :: γ => X.adj p.1 x p.2 ∧ IsGallery p.2 γ

@[expose] def residue (J : Set I) (x : C) : Set C :=
  {y | ∃ γ : List (I × C), X.IsGallery x γ ∧ (∀ i ∈ galleryType γ, i ∈ J) ∧ galleryEnd x γ = y}

@[expose] def Connected : Prop :=
  ∀ x y : C, ∃ γ : List (I × C), X.IsGallery x γ ∧ galleryEnd x γ = y

variable {X}

@[simp] theorem isGallery_nil (x : C) : X.IsGallery x [] := trivial

@[simp] theorem isGallery_cons (x : C) (p : I × C) (γ : List (I × C)) :
    X.IsGallery x (p :: γ) ↔ X.adj p.1 x p.2 ∧ X.IsGallery p.2 γ :=
  Iff.rfl

theorem isGallery_append (x : C) (γ η : List (I × C)) :
    X.IsGallery x (γ ++ η) ↔ X.IsGallery x γ ∧ X.IsGallery (galleryEnd x γ) η := by
  induction γ generalizing x with
  | nil => simp
  | cons p γ ih => simp only [List.cons_append, isGallery_cons, ih, galleryEnd_cons, and_assoc]

theorem isGallery_concat (x : C) (γ : List (I × C)) (p : I × C) :
    X.IsGallery x (γ ++ [p]) ↔ X.IsGallery x γ ∧ X.adj p.1 (galleryEnd x γ) p.2 := by
  rw [isGallery_append]
  simp

theorem IsGallery.append {x : C} {γ η : List (I × C)} (hγ : X.IsGallery x γ)
    (hη : X.IsGallery (galleryEnd x γ) η) : X.IsGallery x (γ ++ η) :=
  (isGallery_append x γ η).mpr ⟨hγ, hη⟩

theorem IsGallery.of_append_left {x : C} {γ η : List (I × C)} (h : X.IsGallery x (γ ++ η)) :
    X.IsGallery x γ :=
  ((isGallery_append x γ η).mp h).1

theorem IsGallery.of_append_right {x : C} {γ η : List (I × C)} (h : X.IsGallery x (γ ++ η)) :
    X.IsGallery (galleryEnd x γ) η :=
  ((isGallery_append x γ η).mp h).2

theorem IsGallery.reverse {x : C} {γ : List (I × C)} (hγ : X.IsGallery x γ) :
    X.IsGallery (galleryEnd x γ) (galleryReverse x γ) := by
  induction γ generalizing x with
  | nil => trivial
  | cons p γ ih =>
    obtain ⟨h1, h2⟩ := hγ
    rw [galleryEnd_cons, galleryReverse_cons, isGallery_concat, galleryEnd_galleryReverse]
    exact ⟨ih h2, adj_symm h1⟩

theorem isGallery_reverse_iff {x : C} {γ : List (I × C)} :
    X.IsGallery (galleryEnd x γ) (galleryReverse x γ) ↔ X.IsGallery x γ := by
  refine ⟨fun h => ?_, IsGallery.reverse⟩
  have := h.reverse
  rwa [galleryEnd_galleryReverse, galleryReverse_galleryReverse] at this

theorem IsGallery.mem_residue {J : Set I} {x : C} {γ : List (I × C)} (hγ : X.IsGallery x γ)
    (hJ : ∀ i ∈ galleryType γ, i ∈ J) : ∀ p ∈ γ, p.2 ∈ X.residue J x := by
  intro p hp
  obtain ⟨γ₁, γ₂, rfl⟩ := List.append_of_mem hp
  refine ⟨γ₁ ++ [p], ((isGallery_append _ _ _).mp (by simpa using hγ)).1, fun i hi => ?_,
    galleryEnd_concat _ _ _⟩
  exact hJ i (by simp only [galleryType_append, List.mem_append] at hi ⊢; simp at hi ⊢; tauto)

theorem galleryEnd_mem_residue {J : Set I} {x : C} {γ : List (I × C)} (hγ : X.IsGallery x γ)
    (hJ : ∀ i ∈ galleryType γ, i ∈ J) : galleryEnd x γ ∈ X.residue J x :=
  ⟨γ, hγ, hJ, rfl⟩

theorem self_mem_residue (J : Set I) (x : C) : x ∈ X.residue J x :=
  ⟨[], trivial, by simp, rfl⟩

theorem mem_residue_trans {J : Set I} {x y z : C} (hxy : y ∈ X.residue J x)
    (hyz : z ∈ X.residue J y) : z ∈ X.residue J x := by
  obtain ⟨γ, hγ, hJ, rfl⟩ := hxy
  obtain ⟨η, hη, hJ', rfl⟩ := hyz
  refine ⟨γ ++ η, hγ.append hη, fun i hi => ?_, galleryEnd_append _ _ _⟩
  rw [galleryType_append, List.mem_append] at hi
  exact hi.elim (hJ i) (hJ' i)

theorem mem_residue_symm {J : Set I} {x y : C} (h : y ∈ X.residue J x) : x ∈ X.residue J y := by
  obtain ⟨γ, hγ, hJ, rfl⟩ := h
  refine ⟨galleryReverse x γ, hγ.reverse, fun i hi => ?_, galleryEnd_galleryReverse _ _⟩
  rw [galleryType_galleryReverse, List.mem_reverse] at hi
  exact hJ i hi

theorem residue_eq_of_mem {J : Set I} {x y : C} (h : y ∈ X.residue J x) :
    X.residue J y = X.residue J x :=
  Set.ext fun _ => ⟨fun hz => mem_residue_trans h hz,
    fun hz => mem_residue_trans (mem_residue_symm h) hz⟩

theorem residue_mono {J K : Set I} (hJK : J ⊆ K) (x : C) : X.residue J x ⊆ X.residue K x :=
  fun _ ⟨γ, hγ, hJ, hend⟩ => ⟨γ, hγ, fun i hi => hJK (hJ i hi), hend⟩

theorem mem_residue_singleton {i : I} {x y : C} : y ∈ X.residue {i} x ↔ X.adj i x y := by
  constructor
  · rintro ⟨γ, hγ, hJ, rfl⟩
    induction γ generalizing x with
    | nil => exact X.adj_refl i x
    | cons p γ ih =>
      obtain ⟨h1, h2⟩ := hγ
      have hp : p.1 = i := by simpa using hJ p.1 (by simp)
      rw [galleryEnd_cons]
      exact adj_trans (hp ▸ h1) (ih h2 fun j hj => hJ j (by simp [hj]))
  · intro h
    exact ⟨[(i, y)], by simpa using h, by simp, rfl⟩

theorem residue_empty (x : C) : X.residue ∅ x = {x} := by
  ext y
  constructor
  · rintro ⟨γ, -, hJ, rfl⟩
    match γ, hJ with
    | [], _ => rfl
    | p :: _, hJ => exact absurd (hJ p.1 (by simp)) (Set.notMem_empty _)
  · rintro rfl
    exact self_mem_residue _ _

@[expose] def IsMorphism (X : ChamberSystem I C) (Y : ChamberSystem I D) (f : C → D) : Prop :=
  ∀ i x y, X.adj i x y → Y.adj i (f x) (f y)

@[expose] def IsResidueIso (X : ChamberSystem I C) (Y : ChamberSystem I D) (f : C → D)
    (J : Set I) (x : C) : Prop :=
  Set.BijOn f (X.residue J x) (Y.residue J (f x)) ∧
    ∀ y ∈ X.residue J x, ∀ z ∈ X.residue J x, ∀ j ∈ J, (Y.adj j (f y) (f z) ↔ X.adj j y z)

variable (X) in
@[expose] def typeAut : Subgroup (Equiv.Perm C) where
  carrier := {g | ∀ i x y, X.adj i (g x) (g y) ↔ X.adj i x y}
  mul_mem' {g h} hg hh i x y := (hg i (h x) (h y)).trans (hh i x y)
  one_mem' _ _ _ := Iff.rfl
  inv_mem' {g} hg i x y := by
    have := hg i (g⁻¹ x) (g⁻¹ y)
    simp only [← Equiv.Perm.mul_apply, mul_inv_cancel, Equiv.Perm.one_apply] at this
    exact this.symm

theorem mem_typeAut {g : Equiv.Perm C} :
    g ∈ X.typeAut ↔ ∀ i x y, X.adj i (g x) (g y) ↔ X.adj i x y :=
  Iff.rfl

theorem isMorphism_of_mem_typeAut {g : Equiv.Perm C} (hg : g ∈ X.typeAut) :
    IsMorphism X X g :=
  fun i x y h => (hg i x y).mpr h

theorem isMorphism_id : IsMorphism X X id := fun _ _ _ h => h

theorem IsMorphism.comp {Y : ChamberSystem I D} {Z : ChamberSystem I E} {f : C → D} {g : D → E}
    (hg : IsMorphism Y Z g) (hf : IsMorphism X Y f) : IsMorphism X Z (g ∘ f) :=
  fun i x y h => hg i _ _ (hf i x y h)

variable {Y : ChamberSystem I D}

theorem IsMorphism.isGallery {f : C → D} (hf : IsMorphism X Y f) {x : C} {γ : List (I × C)}
    (hγ : X.IsGallery x γ) : Y.IsGallery (f x) (galleryMap f γ) := by
  induction γ generalizing x with
  | nil => trivial
  | cons p γ ih => exact ⟨hf _ _ _ hγ.1, ih hγ.2⟩

theorem IsMorphism.mapsTo_residue {f : C → D} (hf : IsMorphism X Y f) (J : Set I) (x : C) :
    Set.MapsTo f (X.residue J x) (Y.residue J (f x)) := by
  rintro _ ⟨γ, hγ, hJ, rfl⟩
  exact ⟨galleryMap f γ, hf.isGallery hγ, by simpa using hJ, galleryEnd_galleryMap f x γ⟩

theorem image_residue_of_mem_typeAut {g : Equiv.Perm C} (hg : g ∈ X.typeAut) (J : Set I)
    (x : C) : g '' X.residue J x = X.residue J (g x) := by
  refine Set.Subset.antisymm (isMorphism_of_mem_typeAut hg |>.mapsTo_residue J x).image_subset
    fun y hy => ⟨g⁻¹ y, ?_, by simp⟩
  have h := (isMorphism_of_mem_typeAut (inv_mem hg)).mapsTo_residue J (g x) hy
  simpa [← Equiv.Perm.mul_apply] using h

theorem IsResidueIso.injOn {f : C → D} {J : Set I} {x : C} (h : IsResidueIso X Y f J x) :
    Set.InjOn f (X.residue J x) :=
  h.1.injOn

theorem isResidueIso_empty (f : C → D) (x : C) : IsResidueIso X Y f ∅ x := by
  refine ⟨?_, fun _ _ _ _ j hj => absurd hj (Set.notMem_empty j)⟩
  rw [residue_empty, residue_empty]
  exact Set.bijOn_singleton.mpr rfl

variable (X) in
inductive ElemMove (x : C) : List (I × C) → List (I × C) → Prop
  | mk (γ₁ η η' γ₂ : List (I × C)) (J : Set I) (hJ : J.encard ≤ 2)
      (hη : X.IsGallery (galleryEnd x γ₁) η) (hη' : X.IsGallery (galleryEnd x γ₁) η')
      (hηJ : ∀ i ∈ galleryType η, i ∈ J) (hη'J : ∀ i ∈ galleryType η', i ∈ J)
      (hend : galleryEnd (galleryEnd x γ₁) η = galleryEnd (galleryEnd x γ₁) η') :
      ElemMove x (γ₁ ++ η ++ γ₂) (γ₁ ++ η' ++ γ₂)

variable (X) in
@[expose] def TwoHomotopic (x : C) : List (I × C) → List (I × C) → Prop :=
  Relation.EqvGen (X.ElemMove x)

variable (X) in
@[expose] def SimplyTwoConnected : Prop :=
  ∀ (x : C) (γ : List (I × C)), X.IsGallery x γ → galleryEnd x γ = x → X.TwoHomotopic x γ []

namespace ElemMove

variable {x : C} {γ γ' : List (I × C)}

theorem symm (h : X.ElemMove x γ γ') : X.ElemMove x γ' γ := by
  obtain ⟨γ₁, η, η', γ₂, J, hJ, hη, hη', hηJ, hη'J, hend⟩ := h
  exact .mk γ₁ η' η γ₂ J hJ hη' hη hη'J hηJ hend.symm

theorem galleryEnd_eq (h : X.ElemMove x γ γ') : galleryEnd x γ = galleryEnd x γ' := by
  obtain ⟨γ₁, η, η', γ₂, J, hJ, hη, hη', hηJ, hη'J, hend⟩ := h
  rw [galleryEnd_append, galleryEnd_append, galleryEnd_append, galleryEnd_append, hend]

theorem isGallery_iff (h : X.ElemMove x γ γ') : X.IsGallery x γ ↔ X.IsGallery x γ' := by
  obtain ⟨γ₁, η, η', γ₂, J, hJ, hη, hη', hηJ, hη'J, hend⟩ := h
  simp only [isGallery_append, galleryEnd_append, hend]
  tauto

theorem append_right (h : X.ElemMove x γ γ') (δ : List (I × C)) :
    X.ElemMove x (γ ++ δ) (γ' ++ δ) := by
  obtain ⟨γ₁, η, η', γ₂, J, hJ, hη, hη', hηJ, hη'J, hend⟩ := h
  simpa only [List.append_assoc] using
    ElemMove.mk (X := X) (x := x) γ₁ η η' (γ₂ ++ δ) J hJ hη hη' hηJ hη'J hend

theorem append_left (α : List (I × C)) (h : X.ElemMove (galleryEnd x α) γ γ') :
    X.ElemMove x (α ++ γ) (α ++ γ') := by
  obtain ⟨γ₁, η, η', γ₂, J, hJ, hη, hη', hηJ, hη'J, hend⟩ := h
  rw [← galleryEnd_append x α γ₁] at hη hη' hend
  simpa only [List.append_assoc] using
    ElemMove.mk (X := X) (x := x) (α ++ γ₁) η η' γ₂ J hJ hη hη' hηJ hη'J hend

theorem map {f : C → D} (hf : IsMorphism X Y f) (h : X.ElemMove x γ γ') :
    Y.ElemMove (f x) (galleryMap f γ) (galleryMap f γ') := by
  obtain ⟨γ₁, η, η', γ₂, J, hJ, hη, hη', hηJ, hη'J, hend⟩ := h
  simp only [galleryMap_append]
  refine .mk _ _ _ _ J hJ ?_ ?_ (by simpa using hηJ) (by simpa using hη'J) ?_
  · rw [galleryEnd_galleryMap]; exact hf.isGallery hη
  · rw [galleryEnd_galleryMap]; exact hf.isGallery hη'
  · rw [galleryEnd_galleryMap, galleryEnd_galleryMap, galleryEnd_galleryMap, hend]

theorem reverse (h : X.ElemMove x γ γ') :
    X.ElemMove (galleryEnd x γ) (galleryReverse x γ) (galleryReverse x γ') := by
  obtain ⟨γ₁, η, η', γ₂, J, hJ, hη, hη', hηJ, hη'J, hend⟩ := h
  have e1 : galleryReverse x (γ₁ ++ η ++ γ₂) = galleryReverse (galleryEnd x (γ₁ ++ η)) γ₂ ++
      galleryReverse (galleryEnd x γ₁) η ++ galleryReverse x γ₁ := by
    rw [galleryReverse_append, galleryReverse_append, List.append_assoc]
  have e2 : galleryReverse x (γ₁ ++ η' ++ γ₂) = galleryReverse (galleryEnd x (γ₁ ++ η)) γ₂ ++
      galleryReverse (galleryEnd x γ₁) η' ++ galleryReverse x γ₁ := by
    rw [galleryReverse_append, galleryReverse_append, List.append_assoc, galleryEnd_append,
      galleryEnd_append, hend]
  rw [e1, e2]
  have hs : galleryEnd (galleryEnd x (γ₁ ++ η ++ γ₂))
      (galleryReverse (galleryEnd x (γ₁ ++ η)) γ₂) = galleryEnd (galleryEnd x γ₁) η := by
    rw [galleryEnd_append _ (γ₁ ++ η), galleryEnd_galleryReverse, galleryEnd_append]
  refine .mk _ _ _ _ J hJ ?_ ?_ ?_ ?_ ?_
  · rw [hs]; exact hη.reverse
  · rw [hs, hend]; exact hη'.reverse
  · simpa using hηJ
  · simpa using hη'J
  · rw [hs, galleryEnd_galleryReverse]
    conv_rhs => rw [hend]
    rw [galleryEnd_galleryReverse]

theorem isGallery (h : X.ElemMove x γ γ') (hγ : X.IsGallery x γ) : X.IsGallery x γ' :=
  h.isGallery_iff.mp hγ

end ElemMove

namespace TwoHomotopic

variable {x : C} {γ γ' γ'' : List (I × C)}

@[refl] protected theorem refl (γ : List (I × C)) : X.TwoHomotopic x γ γ :=
  Relation.EqvGen.refl γ

@[symm] protected theorem symm (h : X.TwoHomotopic x γ γ') : X.TwoHomotopic x γ' γ :=
  Relation.EqvGen.symm _ _ h

@[trans] protected theorem trans (h : X.TwoHomotopic x γ γ') (h' : X.TwoHomotopic x γ' γ'') :
    X.TwoHomotopic x γ γ'' :=
  Relation.EqvGen.trans _ _ _ h h'

theorem of_elemMove (h : X.ElemMove x γ γ') : X.TwoHomotopic x γ γ' :=
  Relation.EqvGen.rel _ _ h

theorem equivalence (x : C) : Equivalence (X.TwoHomotopic x) :=
  Relation.EqvGen.is_equivalence _

theorem reflTransGen_symm (h : Relation.ReflTransGen (X.ElemMove x) γ γ') :
    Relation.ReflTransGen (X.ElemMove x) γ' γ := by
  induction h with
  | refl => exact .refl
  | tail _ h ih => exact Relation.ReflTransGen.head h.symm ih

theorem iff_reflTransGen :
    X.TwoHomotopic x γ γ' ↔ Relation.ReflTransGen (X.ElemMove x) γ γ' := by
  constructor
  · intro h
    induction h with
    | rel _ _ h => exact .single h
    | refl => exact .refl
    | symm _ _ _ ih => exact reflTransGen_symm ih
    | trans _ _ _ _ _ ih ih' => exact ih.trans ih'
  · intro h
    induction h with
    | refl => exact .refl _
    | tail _ h ih => exact ih.trans (of_elemMove h)

theorem galleryEnd_eq (h : X.TwoHomotopic x γ γ') : galleryEnd x γ = galleryEnd x γ' := by
  induction h with
  | rel _ _ h => exact h.galleryEnd_eq
  | refl => rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih ih' => exact ih.trans ih'

theorem isGallery_iff (h : X.TwoHomotopic x γ γ') : X.IsGallery x γ ↔ X.IsGallery x γ' := by
  induction h with
  | rel _ _ h => exact h.isGallery_iff
  | refl => rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih ih' => exact ih.trans ih'

theorem append_right (h : X.TwoHomotopic x γ γ') (δ : List (I × C)) :
    X.TwoHomotopic x (γ ++ δ) (γ' ++ δ) := by
  induction h with
  | rel _ _ h => exact of_elemMove (h.append_right δ)
  | refl => rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih ih' => exact ih.trans ih'

theorem append_left (α : List (I × C)) (h : X.TwoHomotopic (galleryEnd x α) γ γ') :
    X.TwoHomotopic x (α ++ γ) (α ++ γ') := by
  induction h with
  | rel _ _ h => exact of_elemMove (h.append_left α)
  | refl => rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih ih' => exact ih.trans ih'

theorem append {δ δ' : List (I × C)} (h : X.TwoHomotopic x γ γ')
    (h' : X.TwoHomotopic (galleryEnd x γ) δ δ') : X.TwoHomotopic x (γ ++ δ) (γ' ++ δ') :=
  (append_left γ h').trans (h.append_right δ')

theorem map {f : C → D} (hf : IsMorphism X Y f) (h : X.TwoHomotopic x γ γ') :
    Y.TwoHomotopic (f x) (galleryMap f γ) (galleryMap f γ') := by
  induction h with
  | rel _ _ h => exact of_elemMove (h.map hf)
  | refl => rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih ih' => exact ih.trans ih'

theorem reverse (h : X.TwoHomotopic x γ γ') :
    X.TwoHomotopic (galleryEnd x γ) (galleryReverse x γ) (galleryReverse x γ') := by
  induction h with
  | rel _ _ h => exact of_elemMove h.reverse
  | refl => rfl
  | symm a b hab ih =>
    rw [← galleryEnd_eq hab]
    exact ih.symm
  | trans a b c hab _ ih ih' =>
    rw [← galleryEnd_eq hab] at ih'
    exact ih.trans ih'

end TwoHomotopic

theorem twoHomotopic_replace {x : C} (γ₁ η η' γ₂ : List (I × C)) {J : Set I} (hJ : J.encard ≤ 2)
    (hη : X.IsGallery (galleryEnd x γ₁) η) (hη' : X.IsGallery (galleryEnd x γ₁) η')
    (hηJ : ∀ i ∈ galleryType η, i ∈ J) (hη'J : ∀ i ∈ galleryType η', i ∈ J)
    (hend : galleryEnd (galleryEnd x γ₁) η = galleryEnd (galleryEnd x γ₁) η') :
    X.TwoHomotopic x (γ₁ ++ η ++ γ₂) (γ₁ ++ η' ++ γ₂) :=
  .of_elemMove (.mk γ₁ η η' γ₂ J hJ hη hη' hηJ hη'J hend)

theorem encard_singleton_le_two (i : I) : ({i} : Set I).encard ≤ 2 := by
  rw [Set.encard_singleton]
  norm_num

theorem twoHomotopic_panel {x : C} (γ₁ γ₂ : List (I × C)) {i : I} {y z : C}
    (hy : X.adj i (galleryEnd x γ₁) y) (hz : X.adj i y z) :
    X.TwoHomotopic x (γ₁ ++ [(i, y), (i, z)] ++ γ₂) (γ₁ ++ [(i, z)] ++ γ₂) :=
  twoHomotopic_replace γ₁ _ _ γ₂ (encard_singleton_le_two i) (by simpa using ⟨hy, hz⟩)
    (by simpa using adj_trans hy hz) (by simp) (by simp) (by simp)

theorem twoHomotopic_backtrack {x : C} (γ₁ γ₂ : List (I × C)) {i : I} {y : C}
    (hy : X.adj i (galleryEnd x γ₁) y) :
    X.TwoHomotopic x (γ₁ ++ [(i, y), (i, galleryEnd x γ₁)] ++ γ₂) (γ₁ ++ γ₂) := by
  simpa using twoHomotopic_replace (X := X) (x := x) γ₁ [(i, y), (i, galleryEnd x γ₁)] [] γ₂
    (encard_singleton_le_two i) (by simpa using ⟨hy, adj_symm hy⟩) trivial (by simp) (by simp)
    (by simp)

theorem twoHomotopic_constant {x : C} (γ₁ γ₂ : List (I × C)) (i : I) :
    X.TwoHomotopic x (γ₁ ++ [(i, galleryEnd x γ₁)] ++ γ₂) (γ₁ ++ γ₂) := by
  simpa using twoHomotopic_replace (X := X) (x := x) γ₁ [(i, galleryEnd x γ₁)] [] γ₂
    (encard_singleton_le_two i) (by simpa using X.adj_refl i _) trivial (by simp) (by simp)
    (by simp)

theorem twoHomotopic_append_reverse {x : C} {γ : List (I × C)} (hγ : X.IsGallery x γ) :
    X.TwoHomotopic x (γ ++ galleryReverse x γ) [] := by
  induction γ generalizing x with
  | nil => rfl
  | cons p γ ih =>
    obtain ⟨h1, h2⟩ := hγ
    have h3 := (ih h2).append_right [(p.1, x)]
    have h4 := TwoHomotopic.append_left (x := x) [p] h3
    have e : p :: γ ++ galleryReverse x (p :: γ) =
        [p] ++ (γ ++ galleryReverse p.2 γ ++ [(p.1, x)]) := by
      simp
    rw [e]
    refine h4.trans ?_
    simpa using twoHomotopic_backtrack (X := X) (x := x) [] [] (i := p.1) (y := p.2) h1

theorem twoHomotopic_reverse_append {x : C} {γ : List (I × C)} (hγ : X.IsGallery x γ) :
    X.TwoHomotopic (galleryEnd x γ) (galleryReverse x γ ++ γ) [] := by
  have := twoHomotopic_append_reverse hγ.reverse
  rwa [galleryReverse_galleryReverse] at this

variable {Z : ChamberSystem I E}

theorem eq_of_comp_eq (hZ : Z.Connected) {q : D → C} (hq : ∀ i d, Set.InjOn q (Y.residue {i} d))
    {f g : E → D} (hf : IsMorphism Z Y f) (hg : IsMorphism Z Y g) (hfg : ∀ z, q (f z) = q (g z))
    {z₀ : E} (h₀ : f z₀ = g z₀) : f = g := by
  funext z
  obtain ⟨γ, hγ, rfl⟩ := hZ z₀ z
  induction γ generalizing z₀ with
  | nil => exact h₀
  | cons p γ ih =>
    obtain ⟨h1, h2⟩ := hγ
    refine ih ?_ h2
    have hf1 := hf _ _ _ h1
    have hg1 := hg _ _ _ h1
    rw [← h₀] at hg1
    exact hq p.1 (f z₀) (mem_residue_singleton.mpr hf1) (mem_residue_singleton.mpr hg1) (hfg _)

section Lift

variable (Y) in
open _root_.Classical in
@[expose] noncomputable def liftStep (q : D → C) (d : D) (i : I) (y : C) : D :=
  if h : ∃ e, Y.adj i d e ∧ q e = y then h.choose else d

variable (Y) in
@[expose] noncomputable def liftGallery (q : D → C) : D → List (I × C) → List (I × D)
  | _, [] => []
  | d, p :: γ => (p.1, liftStep Y q d p.1 p.2) :: liftGallery q (liftStep Y q d p.1 p.2) γ

@[simp] theorem liftGallery_nil (q : D → C) (d : D) : liftGallery Y q d [] = [] := rfl

@[simp] theorem liftGallery_cons (q : D → C) (d : D) (p : I × C) (γ : List (I × C)) :
    liftGallery Y q d (p :: γ) =
      (p.1, liftStep Y q d p.1 p.2) :: liftGallery Y q (liftStep Y q d p.1 p.2) γ :=
  rfl

theorem liftGallery_append (q : D → C) (d : D) (γ η : List (I × C)) :
    liftGallery Y q d (γ ++ η) =
      liftGallery Y q d γ ++ liftGallery Y q (galleryEnd d (liftGallery Y q d γ)) η := by
  induction γ generalizing d with
  | nil => rfl
  | cons p γ ih => simp [ih]

@[simp] theorem galleryType_liftGallery (q : D → C) (d : D) (γ : List (I × C)) :
    galleryType (liftGallery Y q d γ) = galleryType γ := by
  induction γ generalizing d with
  | nil => rfl
  | cons p γ ih => simp [ih]

variable {q : D → C} (hq : ∀ i d, Set.BijOn q (Y.residue {i} d) (X.residue {i} (q d)))
include hq

theorem liftStep_spec {d : D} {i : I} {y : C} (h : X.adj i (q d) y) :
    Y.adj i d (liftStep Y q d i y) ∧ q (liftStep Y q d i y) = y := by
  have hex : ∃ e, Y.adj i d e ∧ q e = y := by
    obtain ⟨e, he, rfl⟩ := (hq i d).surjOn (mem_residue_singleton.mpr h)
    exact ⟨e, mem_residue_singleton.mp he, rfl⟩
  rw [liftStep, dite_eq_left hex]
  exact hex.choose_spec

theorem eq_liftStep {d e : D} {i : I} (he : Y.adj i d e) :
    e = liftStep Y q d i (q e) := by
  have hqe : X.adj i (q d) (q e) :=
    mem_residue_singleton.mp ((hq i d).mapsTo (mem_residue_singleton.mpr he))
  obtain ⟨h1, h2⟩ := liftStep_spec hq hqe
  exact (hq i d).injOn (mem_residue_singleton.mpr he) (mem_residue_singleton.mpr h1) h2.symm

theorem isGallery_liftGallery {d : D} {γ : List (I × C)} (hγ : X.IsGallery (q d) γ) :
    Y.IsGallery d (liftGallery Y q d γ) ∧ galleryMap q (liftGallery Y q d γ) = γ := by
  induction γ generalizing d with
  | nil => exact ⟨trivial, rfl⟩
  | cons p γ ih =>
    obtain ⟨h1, h2⟩ := hγ
    obtain ⟨hs1, hs2⟩ := liftStep_spec hq h1
    rw [← hs2] at h2
    obtain ⟨ih1, ih2⟩ := ih h2
    refine ⟨⟨hs1, ih1⟩, ?_⟩
    rw [liftGallery_cons, galleryMap_cons, ih2, hs2]

theorem liftGallery_galleryMap {d : D} {Δ : List (I × D)} (hΔ : Y.IsGallery d Δ) :
    liftGallery Y q d (galleryMap q Δ) = Δ := by
  induction Δ generalizing d with
  | nil => rfl
  | cons p Δ ih =>
    obtain ⟨h1, h2⟩ := hΔ
    have he := eq_liftStep hq h1
    rw [galleryMap_cons, liftGallery_cons, ← he, ih h2]

theorem galleryEnd_liftGallery {d : D} {γ : List (I × C)} (hγ : X.IsGallery (q d) γ) :
    q (galleryEnd d (liftGallery Y q d γ)) = galleryEnd (q d) γ := by
  conv_rhs => rw [← (isGallery_liftGallery hq hγ).2]
  rw [galleryEnd_galleryMap]

theorem galleryEnd_liftGallery_eq (hinj : ∀ J : Set I, J.encard ≤ 2 → ∀ d,
      Set.InjOn q (Y.residue J d)) {d : D} {γ γ' : List (I × C)}
    (h : X.TwoHomotopic (q d) γ γ') (hγ : X.IsGallery (q d) γ) :
    galleryEnd d (liftGallery Y q d γ) = galleryEnd d (liftGallery Y q d γ') := by
  rw [TwoHomotopic.iff_reflTransGen] at h
  induction h with
  | refl => rfl
  | @tail γ₁ γ₂ h12 hm ih =>
    rw [ih]
    have hγ₁ : X.IsGallery (q d) γ₁ :=
      (TwoHomotopic.iff_reflTransGen.mpr h12).isGallery_iff.mp hγ
    clear ih h12
    obtain ⟨α, η, η', β, J, hJ, hη, hη', hηJ, hη'J, hend⟩ := hm
    rw [List.append_assoc] at hγ₁
    have hα := hγ₁.of_append_left
    set e := galleryEnd d (liftGallery Y q d α) with he
    have hqe : q e = galleryEnd (q d) α := galleryEnd_liftGallery hq hα
    rw [← hqe] at hη hη' hend
    obtain ⟨hl1, hl2⟩ := isGallery_liftGallery hq hη
    obtain ⟨hl1', hl2'⟩ := isGallery_liftGallery hq hη'
    have key : galleryEnd e (liftGallery Y q e η) = galleryEnd e (liftGallery Y q e η') := by
      refine hinj J hJ e (galleryEnd_mem_residue hl1 (by simpa using hηJ))
        (galleryEnd_mem_residue hl1' (by simpa using hη'J)) ?_
      rw [galleryEnd_liftGallery hq hη, galleryEnd_liftGallery hq hη', hend]
    simp only [liftGallery_append, galleryEnd_append, ← he, key]

end Lift

end ChamberSystem

end CFSG.Monster.B.Geometry
