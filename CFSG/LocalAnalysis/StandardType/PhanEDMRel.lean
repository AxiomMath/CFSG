module

public import CFSG.Monster.B.Geometry.ChamberSystem

public section

namespace CFSG.ClassicalInvolution.Phan.PhanE.DM

open CFSG.Monster.B.Geometry CFSG.Monster.B.Geometry.ChamberSystem

variable {I C : Type*}

@[expose] def GalleryIn (X : ChamberSystem I C) (J : Set I) (A : Set C) (x : C)
    (γ : List (I × C)) : Prop :=
  x ∈ A ∧ X.IsGallery x γ ∧ ∀ p ∈ γ, p.1 ∈ J ∧ p.2 ∈ A

inductive ElemIn (X : ChamberSystem I C) (J : Set I) (A : Set C) (m : ℕ) (x : C) :
    List (I × C) → List (I × C) → Prop
  | mk (γ₁ η η' γ₂ : List (I × C)) (K : Set I) (hK : K.encard ≤ m)
      (hγ : GalleryIn X J A x (γ₁ ++ η ++ γ₂)) (hγ' : GalleryIn X J A x (γ₁ ++ η' ++ γ₂))
      (hηK : ∀ p ∈ η, p.1 ∈ K) (hη'K : ∀ p ∈ η', p.1 ∈ K)
      (hend : galleryEnd (galleryEnd x γ₁) η = galleryEnd (galleryEnd x γ₁) η') :
      ElemIn X J A m x (γ₁ ++ η ++ γ₂) (γ₁ ++ η' ++ γ₂)

@[expose] def HomIn (X : ChamberSystem I C) (J : Set I) (A : Set C) (m : ℕ) (x : C) :
    List (I × C) → List (I × C) → Prop :=
  Relation.EqvGen (ElemIn X J A m x)

@[expose] def ConnectedIn (X : ChamberSystem I C) (J : Set I) (A : Set C) : Prop :=
  ∀ a ∈ A, ∀ b ∈ A, ∃ γ : List (I × C), GalleryIn X J A a γ ∧ galleryEnd a γ = b

@[expose] def SimplyConnectedIn (X : ChamberSystem I C) (J : Set I) (A : Set C) (m : ℕ) : Prop :=
  ∀ (x : C) (γ : List (I × C)), GalleryIn X J A x γ → galleryEnd x γ = x → HomIn X J A m x γ []

variable {X : ChamberSystem I C} {J J' : Set I} {A A' : Set C} {m m' : ℕ} {x : C}
  {γ γ' η η' : List (I × C)}

theorem GalleryIn.mono (hJ : J ⊆ J') (hA : A ⊆ A') (h : GalleryIn X J A x γ) :
    GalleryIn X J' A' x γ :=
  ⟨hA h.1, h.2.1, fun p hp => ⟨hJ (h.2.2 p hp).1, hA (h.2.2 p hp).2⟩⟩

theorem galleryIn_nil : GalleryIn X J A x [] ↔ x ∈ A := by
  simp [GalleryIn]

theorem galleryIn_cons {p : I × C} :
    GalleryIn X J A x (p :: γ) ↔
      x ∈ A ∧ X.adj p.1 x p.2 ∧ p.1 ∈ J ∧ p.2 ∈ A ∧ GalleryIn X J A p.2 γ := by
  simp only [GalleryIn, isGallery_cons, List.forall_mem_cons]
  tauto

theorem galleryIn_append :
    GalleryIn X J A x (γ ++ η) ↔ GalleryIn X J A x γ ∧ GalleryIn X J A (galleryEnd x γ) η := by
  induction γ generalizing x with
  | nil =>
    rw [List.nil_append, galleryEnd_nil, galleryIn_nil]
    exact ⟨fun h => ⟨h.1, h⟩, fun h => h.2⟩
  | cons p γ ih =>
    rw [List.cons_append, galleryIn_cons, galleryIn_cons, galleryEnd_cons, ih]
    tauto

theorem GalleryIn.isGallery (h : GalleryIn X J A x γ) : X.IsGallery x γ := h.2.1

theorem GalleryIn.mem_start (h : GalleryIn X J A x γ) : x ∈ A := h.1

theorem GalleryIn.galleryEnd_mem (h : GalleryIn X J A x γ) : galleryEnd x γ ∈ A := by
  induction γ generalizing x with
  | nil => simpa using GalleryIn.mem_start h
  | cons p γ ih =>
    rw [galleryEnd_cons]
    exact ih (galleryIn_cons.mp h).2.2.2.2

theorem GalleryIn.reverse (h : GalleryIn X J A x γ) :
    GalleryIn X J A (galleryEnd x γ) (galleryReverse x γ) := by
  induction γ generalizing x with
  | nil => exact galleryIn_nil.mpr h.mem_start
  | cons p γ ih =>
    obtain ⟨hxA, hadj, hpJ, hpA, hγ⟩ := galleryIn_cons.mp h
    rw [galleryReverse_cons, galleryEnd_cons]
    refine galleryIn_append.mpr ⟨ih hγ, ?_⟩
    rw [galleryEnd_galleryReverse]
    exact galleryIn_cons.mpr ⟨hpA, adj_symm hadj, hpJ, hxA, galleryIn_nil.mpr hxA⟩

namespace ElemIn

theorem galleryIn_left {a b : List (I × C)} (h : ElemIn X J A m x a b) : GalleryIn X J A x a := by
  obtain ⟨γ₁, η, η', γ₂, K, hK, hγ, hγ', hηK, hη'K, hend⟩ := h
  exact hγ

theorem galleryIn_right {a b : List (I × C)} (h : ElemIn X J A m x a b) :
    GalleryIn X J A x b := by
  obtain ⟨γ₁, η, η', γ₂, K, hK, hγ, hγ', hηK, hη'K, hend⟩ := h
  exact hγ'

theorem galleryEnd_eq {a b : List (I × C)} (h : ElemIn X J A m x a b) :
    galleryEnd x a = galleryEnd x b := by
  obtain ⟨γ₁, η, η', γ₂, K, hK, hγ, hγ', hηK, hη'K, hend⟩ := h
  simp only [galleryEnd_append]
  rw [hend]

end ElemIn

namespace HomIn

theorem of_elemIn {a b : List (I × C)} (h : ElemIn X J A m x a b) : HomIn X J A m x a b :=
  Relation.EqvGen.rel _ _ h

@[refl] protected theorem refl (a : List (I × C)) : HomIn X J A m x a a :=
  Relation.EqvGen.refl a

@[symm] protected theorem symm {a b : List (I × C)} (h : HomIn X J A m x a b) :
    HomIn X J A m x b a :=
  Relation.EqvGen.symm _ _ h

@[trans] protected theorem trans {a b c : List (I × C)} (h : HomIn X J A m x a b)
    (h' : HomIn X J A m x b c) : HomIn X J A m x a c :=
  Relation.EqvGen.trans _ _ _ h h'

theorem galleryEnd_eq (h : HomIn X J A m x γ γ') : galleryEnd x γ = galleryEnd x γ' := by
  induction h with
  | rel a b hab => exact ElemIn.galleryEnd_eq hab
  | refl => rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih ih' => exact ih.trans ih'

theorem galleryIn_iff (h : HomIn X J A m x γ γ') :
    GalleryIn X J A x γ ↔ GalleryIn X J A x γ' := by
  induction h with
  | rel a b hab => exact ⟨fun _ => hab.galleryIn_right, fun _ => hab.galleryIn_left⟩
  | refl => rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih ih' => exact ih.trans ih'

theorem mono (hJ : J ⊆ J') (hA : A ⊆ A') (hm : m ≤ m') (h : HomIn X J A m x γ γ') :
    HomIn X J' A' m' x γ γ' := by
  induction h with
  | rel a b hab =>
    obtain ⟨γ₁, η, η', γ₂, K, hK, hγ, hγ', hηK, hη'K, hend⟩ := hab
    exact Relation.EqvGen.rel _ _ (ElemIn.mk γ₁ η η' γ₂ K
      (hK.trans (Nat.cast_le.mpr hm)) (GalleryIn.mono hJ hA hγ) (GalleryIn.mono hJ hA hγ')
      hηK hη'K hend)
  | refl => exact Relation.EqvGen.refl _
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih ih' => exact ih.trans ih'

private theorem p9uDMR_append_right_aux {a b : List (I × C)}
    (h : HomIn X J A m x a b) :
    ∀ (δ : List (I × C)), GalleryIn X J A (galleryEnd x a) δ →
      HomIn X J A m x (a ++ δ) (b ++ δ) := by
  induction h with
  | rel a b hab =>
    intro δ hδ
    obtain ⟨γ₁, η, η', γ₂, K, hK, hγ, hγ', hηK, hη'K, hend⟩ := hab
    have hδ' : GalleryIn X J A (galleryEnd x (γ₁ ++ η' ++ γ₂)) δ := by
      have he : galleryEnd x (γ₁ ++ η' ++ γ₂) = galleryEnd x (γ₁ ++ η ++ γ₂) := by
        simp only [galleryEnd_append]
        rw [hend]
      rw [he]
      exact hδ
    have hg₁ : GalleryIn X J A x (γ₁ ++ η ++ (γ₂ ++ δ)) := by
      rw [show γ₁ ++ η ++ (γ₂ ++ δ) = (γ₁ ++ η ++ γ₂) ++ δ by
        simp only [List.append_assoc]]
      exact galleryIn_append.mpr ⟨hγ, hδ⟩
    have hg₂ : GalleryIn X J A x (γ₁ ++ η' ++ (γ₂ ++ δ)) := by
      rw [show γ₁ ++ η' ++ (γ₂ ++ δ) = (γ₁ ++ η' ++ γ₂) ++ δ by
        simp only [List.append_assoc]]
      exact galleryIn_append.mpr ⟨hγ', hδ'⟩
    refine Relation.EqvGen.rel _ _ ?_
    simpa only [List.append_assoc] using
      ElemIn.mk (X := X) (x := x) γ₁ η η' (γ₂ ++ δ) K hK hg₁ hg₂ hηK hη'K hend
  | refl => intro δ _; exact Relation.EqvGen.refl _
  | symm a b hab ih =>
    intro δ hδ
    exact (ih δ (by rw [HomIn.galleryEnd_eq hab]; exact hδ)).symm
  | trans a b c hab hbc ih ih' =>
    intro δ hδ
    exact (ih δ hδ).trans (ih' δ (by rw [← HomIn.galleryEnd_eq hab]; exact hδ))

theorem append_right (h : HomIn X J A m x γ γ') {δ : List (I × C)}
    (hδ : GalleryIn X J A (galleryEnd x γ) δ) : HomIn X J A m x (γ ++ δ) (γ' ++ δ) :=
  p9uDMR_append_right_aux h δ hδ

private theorem p9uDMR_append_left_aux {α : List (I × C)} (hα : GalleryIn X J A x α)
    {a b : List (I × C)} (h : HomIn X J A m (galleryEnd x α) a b) :
    HomIn X J A m x (α ++ a) (α ++ b) := by
  induction h with
  | rel a b hab =>
    obtain ⟨γ₁, η, η', γ₂, K, hK, hγ, hγ', hηK, hη'K, hend⟩ := hab
    have hγγ : GalleryIn X J A x ((α ++ γ₁) ++ η ++ γ₂) := by
      simpa only [List.append_assoc] using galleryIn_append.mpr ⟨hα, hγ⟩
    have hγγ' : GalleryIn X J A x ((α ++ γ₁) ++ η' ++ γ₂) := by
      simpa only [List.append_assoc] using galleryIn_append.mpr ⟨hα, hγ'⟩
    refine Relation.EqvGen.rel _ _ ?_
    rw [← galleryEnd_append x α γ₁] at hend
    simpa only [List.append_assoc] using
      ElemIn.mk (X := X) (x := x) (α ++ γ₁) η η' γ₂ K hK hγγ hγγ' hηK hη'K hend
  | refl => exact Relation.EqvGen.refl _
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih ih' => exact ih.trans ih'

theorem append_left {α : List (I × C)} (hα : GalleryIn X J A x α)
    (h : HomIn X J A m (galleryEnd x α) γ γ') : HomIn X J A m x (α ++ γ) (α ++ γ') :=
  p9uDMR_append_left_aux hα h

end HomIn

theorem homIn_replace (γ₁ η η' γ₂ : List (I × C)) {K : Set I} (hK : K.encard ≤ m)
    (hγ : GalleryIn X J A x (γ₁ ++ η ++ γ₂)) (hγ' : GalleryIn X J A x (γ₁ ++ η' ++ γ₂))
    (hηK : ∀ p ∈ η, p.1 ∈ K) (hη'K : ∀ p ∈ η', p.1 ∈ K)
    (hend : galleryEnd (galleryEnd x γ₁) η = galleryEnd (galleryEnd x γ₁) η') :
    HomIn X J A m x (γ₁ ++ η ++ γ₂) (γ₁ ++ η' ++ γ₂) :=
  HomIn.of_elemIn (ElemIn.mk γ₁ η η' γ₂ K hK hγ hγ' hηK hη'K hend)

private theorem p9uDMR_galleryIn_of_append_closed {γ₁ γ₂ μ : List (I × C)}
    (h : GalleryIn X J A x (γ₁ ++ μ ++ γ₂))
    (hend : galleryEnd (galleryEnd x γ₁) μ = galleryEnd x γ₁) :
    GalleryIn X J A x (γ₁ ++ γ₂) := by
  have h1 : GalleryIn X J A x (γ₁ ++ (μ ++ γ₂)) := by
    rw [← List.append_assoc]
    exact h
  have h2 := (galleryIn_append.mp h1).2
  have h3 := (galleryIn_append.mp h2).2
  rw [hend] at h3
  exact galleryIn_append.mpr ⟨(galleryIn_append.mp h1).1, h3⟩

theorem homIn_backtrack (hm : 1 ≤ m) (γ₁ γ₂ : List (I × C)) {i : I} {y : C}
    (hγ : GalleryIn X J A x (γ₁ ++ [(i, y), (i, galleryEnd x γ₁)] ++ γ₂)) :
    HomIn X J A m x (γ₁ ++ [(i, y), (i, galleryEnd x γ₁)] ++ γ₂) (γ₁ ++ γ₂) := by
  have hK : ({i} : Set I).encard ≤ (m : ℕ∞) := by
    rw [Set.encard_singleton]
    exact Nat.one_le_cast.mpr hm
  have hγ' : GalleryIn X J A x (γ₁ ++ [] ++ γ₂) := by
    simpa using p9uDMR_galleryIn_of_append_closed (γ₁ := γ₁) (γ₂ := γ₂) hγ (by simp)
  simpa only [List.append_nil] using
    homIn_replace γ₁ [(i, y), (i, galleryEnd x γ₁)] [] γ₂ hK hγ hγ'
      (by
        intro p hp
        rcases List.mem_cons.mp hp with rfl | hp
        · simp
        · rw [List.mem_singleton] at hp
          rw [hp]
          simp)
      (by simp) (by simp)

theorem homIn_append_reverse (hm : 1 ≤ m) (hγ : GalleryIn X J A x γ) :
    HomIn X J A m x (γ ++ galleryReverse x γ) [] := by
  induction γ generalizing x with
  | nil => exact Relation.EqvGen.refl _
  | cons p γ ih =>
    obtain ⟨hxA, hadj, hpJ, hpA, hγtail⟩ := galleryIn_cons.mp hγ
    have hδ : GalleryIn X J A (galleryEnd p.2 (γ ++ galleryReverse p.2 γ)) [(p.1, x)] := by
      simp only [galleryEnd_append, galleryEnd_galleryReverse]
      exact galleryIn_cons.mpr ⟨hpA, adj_symm hadj, hpJ, hxA, galleryIn_nil.mpr hxA⟩
    have h3 := HomIn.append_right (ih hγtail) hδ
    have hα : GalleryIn X J A x [p] :=
      galleryIn_cons.mpr ⟨hxA, hadj, hpJ, hpA, galleryIn_nil.mpr hpA⟩
    have h4 := HomIn.append_left hα h3
    have hback : GalleryIn X J A x
        ([] ++ [(p.1, p.2), (p.1, galleryEnd x ([] : List (I × C)))] ++ []) := by
      simp only [List.nil_append, galleryEnd_nil, List.append_nil]
      exact galleryIn_cons.mpr ⟨hxA, hadj, hpJ, hpA,
        galleryIn_cons.mpr ⟨hpA, adj_symm hadj, hpJ, hxA, galleryIn_nil.mpr hxA⟩⟩
    have e : p :: γ ++ galleryReverse x (p :: γ) =
        [p] ++ (γ ++ galleryReverse p.2 γ ++ [(p.1, x)]) := by simp
    rw [e]
    exact h4.trans (by simpa using homIn_backtrack (X := X) (x := x) hm [] [] hback)

theorem homIn_iff_append_reverse (hm : 1 ≤ m) (hγ : GalleryIn X J A x γ)
    (hη : GalleryIn X J A x η) (hend : galleryEnd x γ = galleryEnd x η) :
    HomIn X J A m x γ η ↔ HomIn X J A m x (γ ++ galleryReverse x η) [] := by
  constructor
  · intro h
    have hδ : GalleryIn X J A (galleryEnd x γ) (galleryReverse x η) := by
      rw [HomIn.galleryEnd_eq h]
      exact hη.reverse
    exact (HomIn.append_right h hδ).trans (homIn_append_reverse hm hη)
  · intro h
    have hx : galleryEnd x (γ ++ galleryReverse x η) = x := by
      rw [galleryEnd_append, hend, galleryEnd_galleryReverse]
    have hδ : GalleryIn X J A (galleryEnd x (γ ++ galleryReverse x η)) η := by
      rw [hx]
      exact hη
    have h1 : HomIn X J A m x (γ ++ (galleryReverse x η ++ η)) η := by
      simpa only [List.append_assoc, List.nil_append] using HomIn.append_right h hδ
    have hrev : HomIn X J A m (galleryEnd x γ) (galleryReverse x η ++ η) [] := by
      have h' : HomIn X J A m (galleryEnd x η) (galleryReverse x η ++ η) [] := by
        simpa using homIn_append_reverse hm hη.reverse
      rwa [← hend] at h'
    have h2 : HomIn X J A m x (γ ++ (galleryReverse x η ++ η)) γ := by
      simpa using HomIn.append_left hγ hrev
    exact h2.symm.trans h1

end CFSG.ClassicalInvolution.Phan.PhanE.DM
