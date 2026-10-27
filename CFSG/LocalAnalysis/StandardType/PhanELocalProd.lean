module

public import CFSG.LocalAnalysis.StandardType.PhanELocalSys
public import CFSG.ClassicalInvolution.Phan.Frames.Product

public section

namespace CFSG.ClassicalInvolution.Phan.PhanE

open CFSG.Monster.B.Geometry CFSG.Monster.B.Geometry.ChamberSystem

variable {I J C D : Type}

private theorem plp_nil_of_encard {X : ChamberSystem I C} {J : Set I} (hJ : J.encard ≤ 2)
    {x : C} {γ : List (I × C)} (hγ : X.IsGallery x γ)
    (hγJ : ∀ i ∈ galleryType γ, i ∈ J) (hend : galleryEnd x γ = x) :
    X.TwoHomotopic x γ [] := by
  have h : X.TwoHomotopic x ([] ++ γ ++ []) ([] ++ [] ++ []) :=
    twoHomotopic_replace [] γ [] [] hJ (by simpa using hγ) (by simp) hγJ (by simp)
      (by simpa using hend)
  simpa using h

private theorem plp_encard_range_inl_le {α β : Type} (h : (Set.univ : Set α).encard ≤ 2) :
    (Set.range (Sum.inl : α → α ⊕ β)).encard ≤ 2 := by
  rw [Sum.inl_injective.encard_range]
  simpa using h

private theorem plp_encard_range_inr_le {α β : Type} (h : (Set.univ : Set β).encard ≤ 2) :
    (Set.range (Sum.inr : β → α ⊕ β)).encard ≤ 2 := by
  rw [Sum.inr_injective.encard_range]
  simpa using h

private theorem plp_isGallery_liftInl {X : ChamberSystem I C} {Y : ChamberSystem J D}
    {A : Set C} {B : Set D} {b : D} (hb : b ∈ B) :
    ∀ {x : A} {γ : List (I × A)}, (X.restrict A).IsGallery x γ →
      ((X.prod Y).restrict (A ×ˢ B)).IsGallery
        (⟨(x.1, b), Set.mem_prod.mpr ⟨x.2, hb⟩⟩ : ↥(A ×ˢ B))
        (γ.map fun p => ((Sum.inl p.1 : I ⊕ J),
          (⟨(p.2.1, b), Set.mem_prod.mpr ⟨p.2.2, hb⟩⟩ : ↥(A ×ˢ B)))) := by
  intro x γ
  induction γ generalizing x with
  | nil => intro _; exact trivial
  | cons p γ ih =>
    intro hγ
    exact ⟨⟨hγ.1, rfl⟩, ih hγ.2⟩

private theorem plp_galleryEnd_liftInl {X : ChamberSystem I C} {Y : ChamberSystem J D}
    {A : Set C} {B : Set D} {b : D} (hb : b ∈ B) (x : A) (γ : List (I × A)) :
    galleryEnd (⟨(x.1, b), Set.mem_prod.mpr ⟨x.2, hb⟩⟩ : ↥(A ×ˢ B))
        (γ.map fun p => ((Sum.inl p.1 : I ⊕ J),
          (⟨(p.2.1, b), Set.mem_prod.mpr ⟨p.2.2, hb⟩⟩ : ↥(A ×ˢ B))))
      = ⟨((galleryEnd x γ).1, b), Set.mem_prod.mpr ⟨(galleryEnd x γ).2, hb⟩⟩ := by
  induction γ generalizing x with
  | nil => rfl
  | cons p γ ih => exact ih p.2

private theorem plp_isGallery_liftInr {X : ChamberSystem I C} {Y : ChamberSystem J D}
    {A : Set C} {B : Set D} {c : C} (hc : c ∈ A) :
    ∀ {y : B} {γ : List (J × B)}, (Y.restrict B).IsGallery y γ →
      ((X.prod Y).restrict (A ×ˢ B)).IsGallery
        (⟨(c, y.1), Set.mem_prod.mpr ⟨hc, y.2⟩⟩ : ↥(A ×ˢ B))
        (γ.map fun p => ((Sum.inr p.1 : I ⊕ J),
          (⟨(c, p.2.1), Set.mem_prod.mpr ⟨hc, p.2.2⟩⟩ : ↥(A ×ˢ B)))) := by
  intro y γ
  induction γ generalizing y with
  | nil => intro _; exact trivial
  | cons p γ ih =>
    intro hγ
    exact ⟨⟨rfl, hγ.1⟩, ih hγ.2⟩

private theorem plp_galleryEnd_liftInr {X : ChamberSystem I C} {Y : ChamberSystem J D}
    {A : Set C} {B : Set D} {c : C} (hc : c ∈ A) (y : B) (γ : List (J × B)) :
    galleryEnd (⟨(c, y.1), Set.mem_prod.mpr ⟨hc, y.2⟩⟩ : ↥(A ×ˢ B))
        (γ.map fun p => ((Sum.inr p.1 : I ⊕ J),
          (⟨(c, p.2.1), Set.mem_prod.mpr ⟨hc, p.2.2⟩⟩ : ↥(A ×ˢ B))))
      = ⟨(c, (galleryEnd y γ).1), Set.mem_prod.mpr ⟨hc, (galleryEnd y γ).2⟩⟩ := by
  induction γ generalizing y with
  | nil => rfl
  | cons p γ ih => exact ih p.2

theorem connected_prod_restrict {X : ChamberSystem I C} {Y : ChamberSystem J D} {A : Set C}
    {B : Set D} (hA : (X.restrict A).Connected) (hB : (Y.restrict B).Connected) :
    ((X.prod Y).restrict (A ×ˢ B)).Connected := by
  intro x y
  have hxA : x.1.1 ∈ A := (Set.mem_prod.mp x.2).1
  have hxB : x.1.2 ∈ B := (Set.mem_prod.mp x.2).2
  have hyA : y.1.1 ∈ A := (Set.mem_prod.mp y.2).1
  have hyB : y.1.2 ∈ B := (Set.mem_prod.mp y.2).2
  obtain ⟨γ, hγ, hendγ⟩ := hA ⟨x.1.1, hxA⟩ ⟨y.1.1, hyA⟩
  obtain ⟨η, hη, hendη⟩ := hB ⟨x.1.2, hxB⟩ ⟨y.1.2, hyB⟩
  let γ' : List ((I ⊕ J) × ↥(A ×ˢ B)) :=
    γ.map fun p => ((Sum.inl p.1 : I ⊕ J),
      (⟨(p.2.1, x.1.2), Set.mem_prod.mpr ⟨p.2.2, hxB⟩⟩ : ↥(A ×ˢ B)))
  let η' : List ((I ⊕ J) × ↥(A ×ˢ B)) :=
    η.map fun p => ((Sum.inr p.1 : I ⊕ J),
      (⟨(y.1.1, p.2.1), Set.mem_prod.mpr ⟨hyA, p.2.2⟩⟩ : ↥(A ×ˢ B)))
  have hg : galleryEnd x γ' = ⟨(y.1.1, x.1.2), Set.mem_prod.mpr ⟨hyA, hxB⟩⟩ := by
    simpa [γ', hendγ] using plp_galleryEnd_liftInl (X := X) (Y := Y) (A := A) (B := B)
      (b := x.1.2) hxB ⟨x.1.1, hxA⟩ γ
  have hη'end : galleryEnd (galleryEnd x γ') η' = y := by
    rw [hg]
    simpa [η', hendη] using plp_galleryEnd_liftInr (X := X) (Y := Y) (A := A) (B := B)
      (c := y.1.1) hyA ⟨x.1.2, hxB⟩ η
  refine ⟨γ' ++ η', ?_, ?_⟩
  · rw [isGallery_append]
    refine ⟨?_, ?_⟩
    · simpa [γ'] using plp_isGallery_liftInl (X := X) (Y := Y) (A := A) (B := B)
        (b := x.1.2) hxB hγ
    · rw [hg]
      simpa [η'] using plp_isGallery_liftInr (X := X) (Y := Y) (A := A) (B := B)
        (c := y.1.1) hyA hη
  · rw [galleryEnd_append]
    exact hη'end

theorem simplyTwoConnected_prod_restrict (X : ChamberSystem I C) (Y : ChamberSystem J D)
    (A : Set C) (B : Set D) (hI : (Set.univ : Set I).encard ≤ 2)
    (hJ : (Set.univ : Set J).encard ≤ 2) : ((X.prod Y).restrict (A ×ˢ B)).SimplyTwoConnected := by
  intro c γ hγ hend
  refine twoHomotopic_nil_of_union (X := (X.prod Y).restrict (A ×ˢ B))
    (J₁ := Set.range (Sum.inl : I → I ⊕ J)) (J₂ := Set.range (Sum.inr : J → I ⊕ J))
    ?_ ?_ ?_ ?_ c γ hγ ?_ hend
  · intro j hj i hi x y z hxy hyz
    obtain ⟨j', rfl⟩ := hj
    obtain ⟨i', rfl⟩ := hi
    obtain ⟨hxy1, hxy2⟩ := hxy
    obtain ⟨hyz1, hyz2⟩ := hyz
    have h1 : X.adj i' x.1.1 z.1.1 := by rw [hxy1]; exact hyz1
    have h2 : Y.adj j' x.1.2 z.1.2 := by rw [← hyz2]; exact hxy2
    exact ⟨⟨(z.1.1, x.1.2),
      Set.mem_prod.mpr ⟨(Set.mem_prod.mp z.2).1, (Set.mem_prod.mp x.2).2⟩⟩,
      ⟨by simpa using h1, rfl⟩, ⟨rfl, by simpa using h2⟩⟩
  · intro a b h1 h2
    have hb₁ : b.1.2 = a.1.2 :=
      mem_residue_induction (X := (X.prod Y).restrict (A ×ˢ B))
        (J := Set.range (Sum.inl : I → I ⊕ J)) (c := a)
        (fun d => d.1.2 = a.1.2) rfl (fun d e j hj hQ hadj => by
          obtain ⟨i', rfl⟩ := hj
          exact hadj.2.symm.trans hQ) b h1
    have hb₂ : b.1.1 = a.1.1 :=
      mem_residue_induction (X := (X.prod Y).restrict (A ×ˢ B))
        (J := Set.range (Sum.inr : J → I ⊕ J)) (c := a)
        (fun d => d.1.1 = a.1.1) rfl (fun d e j hj hQ hadj => by
          obtain ⟨j', rfl⟩ := hj
          exact hadj.1.symm.trans hQ) b h2
    exact Subtype.ext (Prod.ext hb₂ hb₁)
  · intro a γ hγ hγJ hend
    exact plp_nil_of_encard (X := (X.prod Y).restrict (A ×ˢ B))
      (J := Set.range (Sum.inl : I → I ⊕ J)) (plp_encard_range_inl_le hI) hγ hγJ hend
  · intro a γ hγ hγJ hend
    exact plp_nil_of_encard (X := (X.prod Y).restrict (A ×ˢ B))
      (J := Set.range (Sum.inr : J → I ⊕ J)) (plp_encard_range_inr_le hJ) hγ hγJ hend
  · intro i _
    rcases i with a | b
    · exact Or.inl ⟨a, rfl⟩
    · exact Or.inr ⟨b, rfl⟩

end CFSG.ClassicalInvolution.Phan.PhanE

end
