module

public import CFSG.LocalAnalysis.StandardType.PhanEDMRel
public import Mathlib.Algebra.Order.Ring.Star

public section

namespace CFSG.ClassicalInvolution.Phan.PhanE.DM

open CFSG.Monster.B.Geometry CFSG.Monster.B.Geometry.ChamberSystem

variable {I C : Type*}

structure PushData (X : ChamberSystem I C) (J : Set I) (Q P : Set C) (i : I) (π : C → C)
    (ε : I → C → C → List (I × C)) : Prop where
  mem : ∀ x ∈ Q, π x ∈ P ∧ X.adj i x (π x)
  fix : ∀ x ∈ P, π x = x
  gal : ∀ j ∈ J, ∀ x ∈ Q, ∀ y ∈ Q, X.adj j x y →
    GalleryIn X {i, j} P (π x) (ε j x y) ∧ galleryEnd (π x) (ε j x y) = π y
  id : ∀ j ∈ J, ∀ x ∈ P, ∀ y ∈ P, X.adj j x y → ε j x y = [(j, y)]

@[expose] def push (ε : I → C → C → List (I × C)) : C → List (I × C) → List (I × C)
  | _, [] => []
  | x, p :: γ => ε p.1 x p.2 ++ push ε p.2 γ

variable {X : ChamberSystem I C} {J : Set I} {Q P : Set C} {i : I} {π : C → C}
  {ε : I → C → C → List (I × C)} {x : C} {γ γ' : List (I × C)}

private theorem q2cDMp_pair_encard_le_two (i j : I) : ({i, j} : Set I).encard ≤ 2 := by
  calc ({i, j} : Set I).encard = (insert i ({j} : Set I)).encard := rfl
    _ ≤ ({j} : Set I).encard + 1 := Set.encard_insert_le {j} i
    _ = 2 := by norm_num

private theorem q2cDMp_insert_encard_le_three {K : Set I} (hK : K.encard ≤ 2) (i : I) :
    (insert i K).encard ≤ 3 :=
  calc (insert i K).encard ≤ K.encard + 1 := Set.encard_insert_le K i
    _ ≤ (2 : ℕ∞) + 1 := by simpa only [add_comm] using add_le_add_right hK 1
    _ = 3 := by norm_num

@[simp] theorem push_nil (x : C) : push ε x ([] : List (I × C)) = [] := rfl

@[simp] theorem push_cons (x : C) (p : I × C) (γ : List (I × C)) :
    push ε x (p :: γ) = ε p.1 x p.2 ++ push ε p.2 γ := rfl

theorem push_append (x : C) (γ η : List (I × C)) :
    push ε x (γ ++ η) = push ε x γ ++ push ε (galleryEnd x γ) η := by
  induction γ generalizing x with
  | nil => simp
  | cons p γ ih =>
    simp only [List.cons_append, push_cons, galleryEnd_cons]
    rw [ih, List.append_assoc]

namespace PushData

theorem galleryIn_push (hD : PushData X J Q P i π ε) (hi : i ∈ J)
    (h : GalleryIn X J Q x γ) :
    GalleryIn X J P (π x) (push ε x γ) ∧
      galleryEnd (π x) (push ε x γ) = π (galleryEnd x γ) := by
  induction γ generalizing x with
  | nil =>
    refine ⟨(galleryIn_nil).mpr (hD.mem x h.1).1, rfl⟩
  | cons p γ ih =>
    obtain ⟨hxQ, hxy, hpJ, hyQ, htail⟩ := (galleryIn_cons.mp h)
    have hsub : ({i, p.1} : Set I) ⊆ J := by
      intro a ha
      rcases ha with rfl | rfl
      · exact hi
      · exact hpJ
    obtain ⟨hgal, hend⟩ := hD.gal p.1 hpJ x hxQ p.2 hyQ hxy
    obtain ⟨ihgal, ihend⟩ := ih htail
    simp only [push_cons, galleryEnd_cons]
    constructor
    · rw [galleryIn_append, hend]
      exact ⟨hgal.mono hsub (subset_refl P), ihgal⟩
    · rw [galleryEnd_append, hend, ihend]

theorem push_eq_self (hD : PushData X J Q P i π ε) (h : GalleryIn X J P x γ) :
    push ε x γ = γ := by
  induction γ generalizing x with
  | nil => rfl
  | cons p γ ih =>
    obtain ⟨hxP, hxy, hpJ, hyP, htail⟩ := (galleryIn_cons.mp h)
    rw [push_cons, hD.id p.1 hpJ x hxP p.2 hyP hxy, ih htail]
    rfl

theorem homIn_push (hD : PushData X J Q P i π ε) (hi : i ∈ J) (hPQ : P ⊆ Q)
    (h : GalleryIn X J Q x γ) :
    HomIn X J Q 2 x γ ([(i, π x)] ++ push ε x γ ++ [(i, galleryEnd x γ)]) := by
  induction γ generalizing x with
  | nil =>
    have hxQ : x ∈ Q := h.1
    have hmem := hD.mem x hxQ
    have hgal : GalleryIn X J Q x
        ([(i, π x), (i, galleryEnd x ([] : List (I × C)))] : List (I × C)) := by
      rw [galleryIn_cons, galleryIn_cons, galleryIn_nil]
      exact ⟨hxQ, hmem.2, hi, hPQ hmem.1, hPQ hmem.1, adj_symm hmem.2, hi, hxQ, hxQ⟩
    have hb := homIn_backtrack (X := X) (J := J) (A := Q) (x := x)
      (by norm_num : (1 : ℕ) ≤ 2) ([] : List (I × C)) ([] : List (I × C))
      (i := i) (y := π x) (by simpa using hgal)
    simpa using hb.symm
  | cons p γ ih =>
    obtain ⟨hxQ, hxy, hpJ, hyQ, htail⟩ := (galleryIn_cons.mp h)
    have hsub : ({i, p.1} : Set I) ⊆ J := by
      intro a ha
      rcases ha with rfl | rfl
      · exact hi
      · exact hpJ
    obtain ⟨hgalε, hendε⟩ := hD.gal p.1 hpJ x hxQ p.2 hyQ hxy
    have hε : GalleryIn X J Q (π x) (ε p.1 x p.2) := hgalε.mono hsub hPQ
    have hpgal : GalleryIn X J Q x [p] := by
      rw [galleryIn_cons, galleryIn_nil]
      exact ⟨hxQ, hxy, hpJ, hyQ, hyQ⟩
    have hsingle : GalleryIn X J Q x [(i, π x)] := by
      rw [galleryIn_cons, galleryIn_nil]
      exact ⟨hxQ, (hD.mem x hxQ).2, hi, hPQ (hD.mem x hxQ).1, hPQ (hD.mem x hxQ).1⟩
    have hpushγ := galleryIn_push hD hi htail
    have hpushQ : GalleryIn X J Q (π p.2) (push ε p.2 γ) :=
      hpushγ.1.mono (subset_refl J) hPQ
    have hstep : GalleryIn X J Q (galleryEnd (π p.2) (push ε p.2 γ))
        [(i, galleryEnd p.2 γ)] := by
      have hmem := hD.mem (galleryEnd p.2 γ) (htail.galleryEnd_mem)
      rw [hpushγ.2, galleryIn_cons, galleryIn_nil]
      exact ⟨hPQ hmem.1, adj_symm hmem.2, hi, htail.galleryEnd_mem, htail.galleryEnd_mem⟩
    have hT : GalleryIn X J Q (π p.2) (push ε p.2 γ ++ [(i, galleryEnd p.2 γ)]) :=
      (galleryIn_append).mpr ⟨hpushQ, hstep⟩
    have hright : GalleryIn X J Q x
        (([(i, π x)] ++ ε p.1 x p.2) ++ (push ε p.2 γ ++ [(i, galleryEnd p.2 γ)])) :=
      (galleryIn_append).mpr ⟨(galleryIn_append).mpr ⟨hsingle, hε⟩,
        by rw [galleryEnd_append, galleryEnd_cons, galleryEnd_nil, hendε]; exact hT⟩
    have hih := ih htail
    have h1 : HomIn X J Q 2 x (p :: γ)
        ([(p.1, p.2), (i, π p.2)] ++ (push ε p.2 γ ++ [(i, galleryEnd p.2 γ)])) := by
      have h := HomIn.append_left (X := X) (J := J) (A := Q) (m := 2) (x := x)
        hpgal hih
      simpa [List.singleton_append] using h
    have hleft : GalleryIn X J Q x
        ([(p.1, p.2), (i, π p.2)] ++ (push ε p.2 γ ++ [(i, galleryEnd p.2 γ)])) :=
      h1.galleryIn_iff.mp h
    have hrep : HomIn X J Q 2 x
        ([(p.1, p.2), (i, π p.2)] ++ (push ε p.2 γ ++ [(i, galleryEnd p.2 γ)]))
        (([(i, π x)] ++ ε p.1 x p.2) ++
          (push ε p.2 γ ++ [(i, galleryEnd p.2 γ)])) := by
      refine homIn_replace (X := X) (J := J) (A := Q) (m := 2) (x := x)
        ([] : List (I × C)) ([(p.1, p.2), (i, π p.2)])
        ([(i, π x)] ++ ε p.1 x p.2)
        (push ε p.2 γ ++ [(i, galleryEnd p.2 γ)])
        (q2cDMp_pair_encard_le_two i p.1) hleft hright ?_ ?_ ?_
      · intro q hq
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
        rcases hq with rfl | rfl
        · exact Set.mem_insert_of_mem i rfl
        · exact Set.mem_insert i {p.1}
      · intro q hq
        rw [List.mem_append] at hq
        rcases hq with hq | hq
        · simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
          subst hq
          exact Set.mem_insert i {p.1}
        · exact (hgalε.2.2 q hq).1
      · rw [galleryEnd_cons, galleryEnd_cons, galleryEnd_append, galleryEnd_cons,
          galleryEnd_nil]
        exact hendε.symm
    rw [push_cons, galleryEnd_cons]
    simpa only [List.append_assoc] using h1.trans hrep

theorem mem_insert_of_mem_push (hD : PushData X J Q P i π ε) {K : Set I}
    (h : GalleryIn X J Q x γ) (hK : ∀ q ∈ γ, q.1 ∈ K) :
    ∀ p ∈ push ε x γ, p.1 ∈ insert i K := by
  induction γ generalizing x with
  | nil => simp
  | cons p γ ih =>
    obtain ⟨hxQ, hxy, hpJ, hyQ, htail⟩ := (galleryIn_cons.mp h)
    intro q hq
    rw [push_cons, List.mem_append] at hq
    rcases hq with hq | hq
    · have hgal := (hD.gal p.1 hpJ x hxQ p.2 hyQ hxy).1
      have hmem : q.1 ∈ ({i, p.1} : Set I) := (hgal.2.2 q hq).1
      rcases hmem with hmem | hmem
      · rw [hmem]
        exact Set.mem_insert i K
      · rw [hmem]
        exact Set.mem_insert_of_mem i (hK p (by simp))
    · exact ih htail (fun q hq => hK q (List.mem_cons_of_mem p hq)) q hq

theorem homIn_three_of_homIn_two (hD : PushData X J Q P i π ε) (hi : i ∈ J)
    (h : HomIn X J Q 2 x γ γ') :
    HomIn X J P 3 (π x) (push ε x γ) (push ε x γ') := by
  induction h with
  | rel a b hab =>
    cases hab with
    | mk γ₁ η η' γ₂ K hK hγl hγr hηK hη'K hend =>
      have hpush_a : push ε x (γ₁ ++ η ++ γ₂) =
          push ε x γ₁ ++ push ε (galleryEnd x γ₁) η
            ++ push ε (galleryEnd (galleryEnd x γ₁) η) γ₂ := by
        rw [push_append, push_append, galleryEnd_append, List.append_assoc]
      have hpush_b : push ε x (γ₁ ++ η' ++ γ₂) =
          push ε x γ₁ ++ push ε (galleryEnd x γ₁) η'
            ++ push ε (galleryEnd (galleryEnd x γ₁) η) γ₂ := by
        rw [push_append, push_append, galleryEnd_append, ← hend, List.append_assoc]
      have hgl := galleryIn_push hD hi hγl
      have hγlP : GalleryIn X J P (π x)
          (push ε x γ₁ ++ push ε (galleryEnd x γ₁) η
            ++ push ε (galleryEnd (galleryEnd x γ₁) η) γ₂) := by
        have h := hgl.1
        rwa [hpush_a] at h
      have hgr := galleryIn_push hD hi hγr
      have hγrP : GalleryIn X J P (π x)
          (push ε x γ₁ ++ push ε (galleryEnd x γ₁) η'
            ++ push ε (galleryEnd (galleryEnd x γ₁) η) γ₂) := by
        have h := hgr.1
        rwa [hpush_b] at h
      have hsl₁ := (galleryIn_append).mp hγl
      have hsl₂ := (galleryIn_append).mp hsl₁.1
      have hsr₁ := (galleryIn_append).mp hγr
      have hsr₂ := (galleryIn_append).mp hsr₁.1
      have hrep : HomIn X J P 3 (π x)
          (push ε x γ₁ ++ push ε (galleryEnd x γ₁) η
            ++ push ε (galleryEnd (galleryEnd x γ₁) η) γ₂)
          (push ε x γ₁ ++ push ε (galleryEnd x γ₁) η'
            ++ push ε (galleryEnd (galleryEnd x γ₁) η) γ₂) := by
        refine homIn_replace (X := X) (J := J) (A := P) (m := 3) (x := π x)
          (push ε x γ₁) (push ε (galleryEnd x γ₁) η)
          (push ε (galleryEnd x γ₁) η')
          (push ε (galleryEnd (galleryEnd x γ₁) η) γ₂)
          (q2cDMp_insert_encard_le_three hK i) hγlP hγrP ?_ ?_ ?_
        · exact mem_insert_of_mem_push hD hsl₂.2 hηK
        · exact mem_insert_of_mem_push hD hsr₂.2 hη'K
        · rw [(galleryIn_push hD hi hsl₂.1).2, (galleryIn_push hD hi hsl₂.2).2,
            (galleryIn_push hD hi hsr₂.2).2, hend]
      rw [hpush_a, hpush_b]
      exact hrep
  | refl => exact HomIn.refl _
  | symm a b hab ih => exact ih.symm
  | trans a b c hab hbc ih ih' => exact ih.trans ih'

end PushData

end CFSG.ClassicalInvolution.Phan.PhanE.DM
