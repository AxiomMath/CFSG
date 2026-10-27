module

public import CFSG.LocalAnalysis.StandardType.GGLatRootBridge

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Universal
  CFSG.LieType.RootSystem CFSG.Assembly.LowTwoRank

@[expose] def asClassList : StatedLieTag → List (List (List ℤ))
  | .F4 => [[[2, 3, 4, 2]], [[1, 2, 3, 2]], [[2, 3, 4, 2], [1, 2, 3, 2]],
      [[1, 2, 2, 1], [1, 2, 4, 2]]]
  | .twistedE6 => [[[2, 3, 4, 2]], [[1, 2, 3, 2]], [[1, 2, 2, 1], [1, 2, 4, 2]]]
  | .E6 => [[[1, 2, 2, 3, 2, 1]], [[1, 1, 2, 2, 1, 1], [1, 1, 1, 2, 2, 1]],
      [[0, 1, 1, 2, 2, 1], [1, 1, 1, 2, 1, 1], [1, 1, 2, 2, 1, 0]]]
  | .E7 => [[[2, 2, 3, 4, 3, 2, 1]], [[1, 1, 2, 3, 3, 2, 1], [1, 2, 2, 3, 2, 2, 1]],
      [[1, 2, 2, 3, 2, 1, 0], [1, 1, 2, 2, 2, 2, 1], [1, 1, 2, 3, 2, 1, 1]],
      [[1, 1, 1, 2, 2, 1, 1], [1, 1, 2, 2, 1, 1, 1], [0, 1, 1, 2, 2, 2, 1]],
      [[1, 2, 2, 3, 2, 1, 0], [0, 1, 1, 2, 2, 2, 1], [1, 1, 2, 2, 1, 1, 1],
        [1, 1, 1, 2, 2, 1, 1]]]
  | .E8 => [[[2, 3, 4, 6, 5, 4, 3, 2]], [[2, 2, 4, 5, 4, 3, 2, 1], [2, 3, 3, 5, 4, 3, 2, 1]],
      [[2, 2, 3, 4, 3, 2, 2, 1], [1, 2, 3, 4, 3, 3, 2, 1], [1, 2, 2, 4, 4, 3, 2, 1]],
      [[2, 2, 3, 4, 3, 2, 1, 0], [1, 2, 3, 4, 3, 2, 1, 1], [1, 2, 2, 3, 3, 3, 2, 1],
        [1, 2, 2, 4, 3, 2, 2, 1]]]
  | _ => []

section Orth

@[expose] def ggASClass (t : StatedLieTag) (n f : ℕ) (Z : Set (Fin (ggU t n f).D.rank → ℤ)) : Prop :=
  ∃ L ∈ asClassList t, Z = {β | List.ofFn β ∈ L}

private def vecOf (N : ℕ) (ℓ : List ℤ) : Fin N → ℤ := fun i => ℓ.getD i.val 0

private theorem vecOf_ofFn {N : ℕ} (β : Fin N → ℤ) : vecOf N (List.ofFn β) = β := by
  funext i
  simp only [vecOf]
  rw [List.getD_eq_get (l := List.ofFn β) (d := (0 : ℤ))
    (i := ⟨i.val, by rw [List.length_ofFn]; exact i.isLt⟩)]
  rw [List.get_ofFn]
  exact congrArg β (Fin.ext rfl)

private abbrev tagOf : StatedLieTag → Tag
  | .F4 => .F4
  | .E6 => .E6
  | .E7 => .E7
  | .E8 => .E8
  | .twistedE6 => .F4
  | _ => .F4

private def e4 (j : Fin (Tag.rank .F4)) : Fin (Tag.rank .F4) → ℤ := Pi.single j 1

private def e6 (j : Fin (Tag.rank .E6)) : Fin (Tag.rank .E6) → ℤ := Pi.single j 1

private def e7 (j : Fin (Tag.rank .E7)) : Fin (Tag.rank .E7) → ℤ := Pi.single j 1

private def e8 (j : Fin (Tag.rank .E8)) : Fin (Tag.rank .E8) → ℤ := Pi.single j 1

private def f4Highest : Fin (Tag.rank .F4) → ℤ := ![2, 3, 4, 2]

private def classRootsB (t : StatedLieTag) (L : List (List ℤ)) : Bool :=
  L.all fun ℓ => decide (vecOf (tagOf t).rank ℓ ∈ rootFinset (tagOf t))

private theorem classRootsB_sound {t : StatedLieTag} {L : List (List ℤ)}
    (h : classRootsB t L = true) (ℓ : List ℤ) (hℓ : ℓ ∈ L) :
    vecOf (tagOf t).rank ℓ ∈ rootFinset (tagOf t) :=
  of_decide_eq_true (List.all_eq_true.mp h ℓ hℓ)

private theorem classRootsB_sound_wrap {t : StatedLieTag} {L : List (List ℤ)}
    (h : classRootsB t L = true) (β : Fin (tagOf t).rank → ℤ) (hβ : List.ofFn β ∈ L) :
    β ∈ rootFinset (tagOf t) := by
  have h' := classRootsB_sound h (List.ofFn β) hβ
  have heq : vecOf (tagOf t).rank (List.ofFn β) = β := vecOf_ofFn β
  rwa [heq] at h'

private def allClassRootsB (t : StatedLieTag) : Bool :=
  (asClassList t).all fun L => classRootsB t L

private theorem allClassRootsB_sound {t : StatedLieTag} (h : allClassRootsB t = true)
    {L : List (List ℤ)} (hL : L ∈ asClassList t) : classRootsB t L = true :=
  List.all_eq_true.mp h L hL

private def classOrthB (t : StatedLieTag) (L : List (List ℤ)) (j : Fin (tagOf t).rank) : Bool :=
  L.all fun ℓ => decide (
    (Pi.single j 1 : Fin (tagOf t).rank → ℤ) ≠ vecOf (tagOf t).rank ℓ ∧
    (Pi.single j 1 : Fin (tagOf t).rank → ℤ) ≠ -vecOf (tagOf t).rank ℓ ∧
    (Pi.single j 1 + vecOf (tagOf t).rank ℓ) ∉ rootFinset (tagOf t) ∧
    (Pi.single j 1 - vecOf (tagOf t).rank ℓ) ∉ rootFinset (tagOf t))

private theorem classOrthB_sound {t : StatedLieTag} {L : List (List ℤ)} {j : Fin (tagOf t).rank}
    (h : classOrthB t L j = true) (ℓ : List ℤ) (hℓ : ℓ ∈ L) :
    (Pi.single j 1 : Fin (tagOf t).rank → ℤ) ≠ vecOf (tagOf t).rank ℓ ∧
    (Pi.single j 1 : Fin (tagOf t).rank → ℤ) ≠ -vecOf (tagOf t).rank ℓ ∧
    (Pi.single j 1 + vecOf (tagOf t).rank ℓ) ∉ rootFinset (tagOf t) ∧
    (Pi.single j 1 - vecOf (tagOf t).rank ℓ) ∉ rootFinset (tagOf t) :=
  of_decide_eq_true (List.all_eq_true.mp h ℓ hℓ)

private theorem classOrthB_sound_wrap {t : StatedLieTag} {L : List (List ℤ)} {j : Fin (tagOf t).rank}
    (h : classOrthB t L j = true) (β : Fin (tagOf t).rank → ℤ) (hβ : List.ofFn β ∈ L) :
    (Pi.single j 1 : Fin (tagOf t).rank → ℤ) ≠ β ∧
    (Pi.single j 1 : Fin (tagOf t).rank → ℤ) ≠ -β ∧
    (Pi.single j 1 + β) ∉ rootFinset (tagOf t) ∧
    (Pi.single j 1 - β) ∉ rootFinset (tagOf t) := by
  have h' := classOrthB_sound h (List.ofFn β) hβ
  have heq : vecOf (tagOf t).rank (List.ofFn β) = β := vecOf_ofFn β
  rwa [heq] at h'

private theorem ggRootClass_of_mem {t : StatedLieTag} {n f : ℕ} (h : ¬ GGTwistedTag t)
    {α : Fin (ggU t n f).D.rank → ℤ} (hα : α ∈ (ggU t n f).D.roots) :
    GGRootClass (ggU t n f).D t α :=
  ⟨hα, fun htw => absurd htw h⟩

private theorem f4_height_le_rootFinset :
    ∀ v ∈ rootFinset Tag.F4, (∑ i, v i) ≤ 11 := by decide +kernel

private theorem e4_mem_rootFinset (j : Fin (Tag.rank .F4)) : e4 j ∈ rootFinset Tag.F4 :=
  mem_rootFinset.2 (IsRoot.basis j)

private theorem e6_mem_rootFinset (j : Fin (Tag.rank .E6)) : e6 j ∈ rootFinset Tag.E6 :=
  mem_rootFinset.2 (IsRoot.basis j)

private theorem e7_mem_rootFinset (j : Fin (Tag.rank .E7)) : e7 j ∈ rootFinset Tag.E7 :=
  mem_rootFinset.2 (IsRoot.basis j)

private theorem e8_mem_rootFinset (j : Fin (Tag.rank .E8)) : e8 j ∈ rootFinset Tag.E8 :=
  mem_rootFinset.2 (IsRoot.basis j)

private theorem e4_mem_roots_F4 (n f : ℕ) (j : Fin (Tag.rank .F4)) :
    e4 j ∈ (ggU .F4 n f).D.roots :=
  (mem_roots_F4 n f (e4 j)).2 (e4_mem_rootFinset j)

private theorem e6_mem_roots_E6 (n f : ℕ) (j : Fin (Tag.rank .E6)) :
    e6 j ∈ (ggU .E6 n f).D.roots :=
  (mem_roots_E6 n f (e6 j)).2 (e6_mem_rootFinset j)

private theorem e7_mem_roots_E7 (n f : ℕ) (j : Fin (Tag.rank .E7)) :
    e7 j ∈ (ggU .E7 n f).D.roots :=
  (mem_roots_E7 n f (e7 j)).2 (e7_mem_rootFinset j)

private theorem e8_mem_roots_E8 (n f : ℕ) (j : Fin (Tag.rank .E8)) :
    e8 j ∈ (ggU .E8 n f).D.roots :=
  (mem_roots_E8 n f (e8 j)).2 (e8_mem_rootFinset j)

private theorem e4_mem_roots_twistedE6 (n f : ℕ) (j : Fin (Tag.rank .F4)) :
    e4 j ∈ (ggU .twistedE6 n f).D.roots :=
  (mem_roots_twistedE6 n f (e4 j)).2 (e4_mem_rootFinset j)

private theorem f4Highest_mem : f4Highest ∈ rootFinset Tag.F4 := by decide +kernel

private theorem stronglyOrth_F4 (n f : ℕ) {j : Fin (Tag.rank .F4)}
    {β : Fin (Tag.rank .F4) → ℤ}
    (h : (Pi.single j 1 : Fin (Tag.rank .F4) → ℤ) ≠ β ∧
      (Pi.single j 1 : Fin (Tag.rank .F4) → ℤ) ≠ -β ∧
      (Pi.single j 1 + β) ∉ rootFinset Tag.F4 ∧
      (Pi.single j 1 - β) ∉ rootFinset Tag.F4) :
    StronglyOrth (ggU .F4 n f).D (Pi.single j 1) β := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  refine ⟨h1, h2, ?_, ?_⟩
  · intro hmem
    exact h3 ((mem_roots_F4 n f ((Pi.single j 1 : Fin (Tag.rank .F4) → ℤ) + β)).1 hmem)
  · intro hmem
    exact h4 ((mem_roots_F4 n f ((Pi.single j 1 : Fin (Tag.rank .F4) → ℤ) - β)).1 hmem)

private theorem stronglyOrth_E6 (n f : ℕ) {j : Fin (Tag.rank .E6)}
    {β : Fin (Tag.rank .E6) → ℤ}
    (h : (Pi.single j 1 : Fin (Tag.rank .E6) → ℤ) ≠ β ∧
      (Pi.single j 1 : Fin (Tag.rank .E6) → ℤ) ≠ -β ∧
      (Pi.single j 1 + β) ∉ rootFinset Tag.E6 ∧
      (Pi.single j 1 - β) ∉ rootFinset Tag.E6) :
    StronglyOrth (ggU .E6 n f).D (Pi.single j 1) β := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  refine ⟨h1, h2, ?_, ?_⟩
  · intro hmem
    exact h3 ((mem_roots_E6 n f ((Pi.single j 1 : Fin (Tag.rank .E6) → ℤ) + β)).1 hmem)
  · intro hmem
    exact h4 ((mem_roots_E6 n f ((Pi.single j 1 : Fin (Tag.rank .E6) → ℤ) - β)).1 hmem)

private theorem stronglyOrth_E7 (n f : ℕ) {j : Fin (Tag.rank .E7)}
    {β : Fin (Tag.rank .E7) → ℤ}
    (h : (Pi.single j 1 : Fin (Tag.rank .E7) → ℤ) ≠ β ∧
      (Pi.single j 1 : Fin (Tag.rank .E7) → ℤ) ≠ -β ∧
      (Pi.single j 1 + β) ∉ rootFinset Tag.E7 ∧
      (Pi.single j 1 - β) ∉ rootFinset Tag.E7) :
    StronglyOrth (ggU .E7 n f).D (Pi.single j 1) β := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  refine ⟨h1, h2, ?_, ?_⟩
  · intro hmem
    exact h3 ((mem_roots_E7 n f ((Pi.single j 1 : Fin (Tag.rank .E7) → ℤ) + β)).1 hmem)
  · intro hmem
    exact h4 ((mem_roots_E7 n f ((Pi.single j 1 : Fin (Tag.rank .E7) → ℤ) - β)).1 hmem)

private theorem stronglyOrth_E8 (n f : ℕ) {j : Fin (Tag.rank .E8)}
    {β : Fin (Tag.rank .E8) → ℤ}
    (h : (Pi.single j 1 : Fin (Tag.rank .E8) → ℤ) ≠ β ∧
      (Pi.single j 1 : Fin (Tag.rank .E8) → ℤ) ≠ -β ∧
      (Pi.single j 1 + β) ∉ rootFinset Tag.E8 ∧
      (Pi.single j 1 - β) ∉ rootFinset Tag.E8) :
    StronglyOrth (ggU .E8 n f).D (Pi.single j 1) β := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  refine ⟨h1, h2, ?_, ?_⟩
  · intro hmem
    exact h3 ((mem_roots_E8 n f ((Pi.single j 1 : Fin (Tag.rank .E8) → ℤ) + β)).1 hmem)
  · intro hmem
    exact h4 ((mem_roots_E8 n f ((Pi.single j 1 : Fin (Tag.rank .E8) → ℤ) - β)).1 hmem)

private theorem stronglyOrth_twistedE6 (n f : ℕ) {j : Fin (Tag.rank .F4)}
    {β : Fin (Tag.rank .F4) → ℤ}
    (h : (Pi.single j 1 : Fin (Tag.rank .F4) → ℤ) ≠ β ∧
      (Pi.single j 1 : Fin (Tag.rank .F4) → ℤ) ≠ -β ∧
      (Pi.single j 1 + β) ∉ rootFinset Tag.F4 ∧
      (Pi.single j 1 - β) ∉ rootFinset Tag.F4) :
    StronglyOrth (ggU .twistedE6 n f).D (Pi.single j 1) β := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  refine ⟨h1, h2, ?_, ?_⟩
  · intro hmem
    exact h3 ((mem_roots_twistedE6 n f
      ((Pi.single j 1 : Fin (Tag.rank .F4) → ℤ) + β)).1 hmem)
  · intro hmem
    exact h4 ((mem_roots_twistedE6 n f
      ((Pi.single j 1 : Fin (Tag.rank .F4) → ℤ) - β)).1 hmem)

private abbrev f4FiniteType : TauCeti.IsFiniteType (Tag.cartan .F4) :=
  CFSG.LieType.Chevalley.isFiniteType_cartan .F4

private abbrev f4Datum : UniversalRootDatum (Multiplicative (ZMod 2)) where
  rank := Tag.rank .F4
  cartan := Tag.cartan .F4
  isFiniteType := f4FiniteType
  divisible := ∅
  rootGroup := fun _ => ⊥

private noncomputable def f4WordE1 : (coxeterMatrix f4Datum.isFiniteType).Group :=
  (coxeterMatrix f4Datum.isFiniteType).toCoxeterSystem.simple ⟨2, by decide⟩ *
    (coxeterMatrix f4Datum.isFiniteType).toCoxeterSystem.simple ⟨3, by decide⟩ *
    (coxeterMatrix f4Datum.isFiniteType).toCoxeterSystem.simple ⟨0, by decide⟩ *
    (coxeterMatrix f4Datum.isFiniteType).toCoxeterSystem.simple ⟨1, by decide⟩ *
    (coxeterMatrix f4Datum.isFiniteType).toCoxeterSystem.simple ⟨2, by decide⟩ *
    (coxeterMatrix f4Datum.isFiniteType).toCoxeterSystem.simple ⟨1, by decide⟩ *
    (coxeterMatrix f4Datum.isFiniteType).toCoxeterSystem.simple ⟨0, by decide⟩

private noncomputable def f4WordE0 : (coxeterMatrix f4Datum.isFiniteType).Group :=
  (coxeterMatrix f4Datum.isFiniteType).toCoxeterSystem.simple ⟨1, by decide⟩ *
    (coxeterMatrix f4Datum.isFiniteType).toCoxeterSystem.simple ⟨2, by decide⟩ *
    (coxeterMatrix f4Datum.isFiniteType).toCoxeterSystem.simple ⟨3, by decide⟩ *
    (coxeterMatrix f4Datum.isFiniteType).toCoxeterSystem.simple ⟨1, by decide⟩ *
    (coxeterMatrix f4Datum.isFiniteType).toCoxeterSystem.simple ⟨2, by decide⟩ *
    (coxeterMatrix f4Datum.isFiniteType).toCoxeterSystem.simple ⟨1, by decide⟩ *
    (coxeterMatrix f4Datum.isFiniteType).toCoxeterSystem.simple ⟨0, by decide⟩

private theorem f4_word_e1 :
    weylAction f4Datum.isFiniteType f4WordE1 f4Highest =
      Pi.single (⟨1, by decide⟩ : Fin (Tag.rank .F4)) 1 := by
  simp only [f4WordE1, weylAction_mul_apply, weylAction_simple, reflection_apply]
  decide +kernel

private theorem f4_word_e0 :
    weylAction f4Datum.isFiniteType f4WordE0 f4Highest =
      Pi.single (⟨0, by decide⟩ : Fin (Tag.rank .F4)) 1 := by
  simp only [f4WordE0, weylAction_mul_apply, weylAction_simple, reflection_apply]
  decide +kernel

private theorem f4Highest_mem_datum : f4Highest ∈ f4Datum.roots := by
  show f4Highest ∈ CFSG.LieType.RootSystem.roots f4FiniteType ∅
  exact (CFSG.LieType.Chevalley.isRoot_iff_mem_roots (τ := .F4)).1 (mem_rootFinset.1 f4Highest_mem)

private theorem f4Datum_height_le :
    ∀ v ∈ f4Datum.roots, (∑ i, v i) ≤ 11 := by
  intro v hv
  have hv' : v ∈ CFSG.LieType.RootSystem.roots f4FiniteType ∅ := hv
  exact f4_height_le_rootFinset v
    (mem_rootFinset.2 ((CFSG.LieType.Chevalley.isRoot_iff_mem_roots (τ := .F4)).2 hv'))

private theorem f4_longRoot_e1 : GGLongRoot f4Datum (e4 ⟨1, by decide⟩) :=
  ⟨f4WordE1, f4Highest, f4Highest_mem_datum, f4Datum_height_le, f4_word_e1.symm⟩

private theorem f4_longRoot_e0 : GGLongRoot f4Datum (e4 ⟨0, by decide⟩) :=
  ⟨f4WordE0, f4Highest, f4Highest_mem_datum, f4Datum_height_le, f4_word_e0.symm⟩

private theorem twistedE6_longRoot_e1 (n f : ℕ) :
    GGLongRoot (ggU .twistedE6 n f).D (e4 ⟨1, by decide⟩) := by
  change GGLongRoot f4Datum (e4 ⟨1, by decide⟩)
  exact f4_longRoot_e1

private theorem twistedE6_longRoot_e0 (n f : ℕ) :
    GGLongRoot (ggU .twistedE6 n f).D (e4 ⟨0, by decide⟩) := by
  change GGLongRoot f4Datum (e4 ⟨0, by decide⟩)
  exact f4_longRoot_e0

theorem ggASClass_subset_roots (t : StatedLieTag) (n f : ℕ) (ht : GGExcFive t)
    (Z : Set (Fin (ggU t n f).D.rank → ℤ)) (hZ : ggASClass t n f Z) : Z ⊆ (ggU t n f).D.roots := by
  obtain ⟨L, hL, rfl⟩ := hZ
  intro β hβ
  unfold GGExcFive at ht
  rcases ht with rfl | rfl | rfl | rfl | rfl
  · exact (mem_roots_F4 n f β).2
      (classRootsB_sound_wrap (allClassRootsB_sound (by decide +kernel) hL) β hβ)
  · exact (mem_roots_E6 n f β).2
      (classRootsB_sound_wrap (allClassRootsB_sound (by decide +kernel) hL) β hβ)
  · exact (mem_roots_E7 n f β).2
      (classRootsB_sound_wrap (allClassRootsB_sound (by decide +kernel) hL) β hβ)
  · exact (mem_roots_E8 n f β).2
      (classRootsB_sound_wrap (allClassRootsB_sound (by decide +kernel) hL) β hβ)
  · exact (mem_roots_twistedE6 n f β).2
      (classRootsB_sound_wrap (allClassRootsB_sound (by decide +kernel) hL) β hβ)

@[expose] def GGLatOrthExc
    (ASClass : ∀ (t : StatedLieTag) (n f : ℕ), Set (Fin (ggU t n f).D.rank → ℤ) → Prop) : Prop :=
  ∀ (t : StatedLieTag) (n f : ℕ), GGExcFive t → ∀ Z, ASClass t n f Z →
    ∃ α ∈ (ggU t n f).D.roots, GGRootClass (ggU t n f).D t α ∧
      ∀ β ∈ Z, StronglyOrth (ggU t n f).D α β

private theorem classOrthB_check_1 :
    classOrthB .F4 [[2, 3, 4, 2]] ⟨1, by decide⟩ = true := by decide +kernel
private theorem classOrthB_check_2 :
    classOrthB .F4 [[1, 2, 3, 2]] ⟨1, by decide⟩ = true := by decide +kernel
private theorem classOrthB_check_3 :
    classOrthB .F4 [[2, 3, 4, 2], [1, 2, 3, 2]] ⟨1, by decide⟩ = true := by decide +kernel
private theorem classOrthB_check_4 :
    classOrthB .F4 [[1, 2, 2, 1], [1, 2, 4, 2]] ⟨0, by decide⟩ = true := by decide +kernel
private theorem classOrthB_check_5 :
    classOrthB .E6 [[1, 2, 2, 3, 2, 1]] ⟨5, by decide⟩ = true := by decide +kernel
private theorem classOrthB_check_6 :
    classOrthB .E6 [[1, 1, 2, 2, 1, 1], [1, 1, 1, 2, 2, 1]] ⟨3, by decide⟩ = true := by decide +kernel
private theorem classOrthB_check_7 :
    classOrthB .E6 [[0, 1, 1, 2, 2, 1], [1, 1, 1, 2, 1, 1], [1, 1, 2, 2, 1, 0]] ⟨1, by decide⟩ = true := by decide +kernel
private theorem classOrthB_check_8 :
    classOrthB .E7 [[2, 2, 3, 4, 3, 2, 1]] ⟨6, by decide⟩ = true := by decide +kernel
private theorem classOrthB_check_9 :
    classOrthB .E7 [[1, 1, 2, 3, 3, 2, 1], [1, 2, 2, 3, 2, 2, 1]] ⟨6, by decide⟩ = true := by decide +kernel
private theorem classOrthB_check_10 :
    classOrthB .E7 [[1, 2, 2, 3, 2, 1, 0], [1, 1, 2, 2, 2, 2, 1], [1, 1, 2, 3, 2, 1, 1]] ⟨4, by decide⟩ = true := by decide +kernel
private theorem classOrthB_check_11 :
    classOrthB .E7 [[1, 1, 1, 2, 2, 1, 1], [1, 1, 2, 2, 1, 1, 1], [0, 1, 1, 2, 2, 2, 1]] ⟨3, by decide⟩ = true := by decide +kernel
private theorem classOrthB_check_12 :
    classOrthB .E7 [[1, 2, 2, 3, 2, 1, 0], [0, 1, 1, 2, 2, 2, 1], [1, 1, 2, 2, 1, 1, 1], [1, 1, 1, 2, 2, 1, 1]] ⟨3, by decide⟩ = true := by decide +kernel
private theorem classOrthB_check_13 :
    classOrthB .E8 [[2, 3, 4, 6, 5, 4, 3, 2]] ⟨6, by decide⟩ = true := by decide +kernel
private theorem classOrthB_check_14 :
    classOrthB .E8 [[2, 2, 4, 5, 4, 3, 2, 1], [2, 3, 3, 5, 4, 3, 2, 1]] ⟨7, by decide⟩ = true := by decide +kernel
private theorem classOrthB_check_15 :
    classOrthB .E8 [[2, 2, 3, 4, 3, 2, 2, 1], [1, 2, 3, 4, 3, 3, 2, 1], [1, 2, 2, 4, 4, 3, 2, 1]] ⟨7, by decide⟩ = true := by decide +kernel
private theorem classOrthB_check_16 :
    classOrthB .E8 [[2, 2, 3, 4, 3, 2, 1, 0], [1, 2, 3, 4, 3, 2, 1, 1], [1, 2, 2, 3, 3, 3, 2, 1], [1, 2, 2, 4, 3, 2, 2, 1]] ⟨4, by decide⟩ = true := by decide +kernel
private theorem classOrthB_check_17 :
    classOrthB .twistedE6 [[2, 3, 4, 2]] ⟨1, by decide⟩ = true := by decide +kernel
private theorem classOrthB_check_18 :
    classOrthB .twistedE6 [[1, 2, 3, 2]] ⟨1, by decide⟩ = true := by decide +kernel
private theorem classOrthB_check_19 :
    classOrthB .twistedE6 [[1, 2, 2, 1], [1, 2, 4, 2]] ⟨0, by decide⟩ = true := by decide +kernel

theorem ggLatOrthExc_holds : GGLatOrthExc ggASClass := by
  intro t n f ht Z hZ
  obtain ⟨L, hL, rfl⟩ := hZ
  unfold GGExcFive at ht
  rcases ht with rfl | rfl | rfl | rfl | rfl
  ·
    simp [asClassList] at hL
    rcases hL with rfl | rfl | rfl | rfl
    · have hα : e4 ⟨1, by decide⟩ ∈ (ggU .F4 n f).D.roots :=
        e4_mem_roots_F4 n f ⟨1, by decide⟩
      refine ⟨e4 ⟨1, by decide⟩, hα, ?_, ?_⟩
      · exact ggRootClass_of_mem (by simp [GGTwistedTag]) hα
      · intro β hβ
        have hcheck : classOrthB .F4 [[2, 3, 4, 2]] ⟨1, by decide⟩ = true := classOrthB_check_1
        exact stronglyOrth_F4 n f (classOrthB_sound_wrap hcheck β hβ)
    · have hα : e4 ⟨1, by decide⟩ ∈ (ggU .F4 n f).D.roots :=
        e4_mem_roots_F4 n f ⟨1, by decide⟩
      refine ⟨e4 ⟨1, by decide⟩, hα, ?_, ?_⟩
      · exact ggRootClass_of_mem (by simp [GGTwistedTag]) hα
      · intro β hβ
        have hcheck : classOrthB .F4 [[1, 2, 3, 2]] ⟨1, by decide⟩ = true := classOrthB_check_2
        exact stronglyOrth_F4 n f (classOrthB_sound_wrap hcheck β hβ)
    · have hα : e4 ⟨1, by decide⟩ ∈ (ggU .F4 n f).D.roots :=
        e4_mem_roots_F4 n f ⟨1, by decide⟩
      refine ⟨e4 ⟨1, by decide⟩, hα, ?_, ?_⟩
      · exact ggRootClass_of_mem (by simp [GGTwistedTag]) hα
      · intro β hβ
        have hcheck : classOrthB .F4 [[2, 3, 4, 2], [1, 2, 3, 2]] ⟨1, by decide⟩ = true := classOrthB_check_3
        exact stronglyOrth_F4 n f (classOrthB_sound_wrap hcheck β hβ)
    · have hα : e4 ⟨0, by decide⟩ ∈ (ggU .F4 n f).D.roots :=
        e4_mem_roots_F4 n f ⟨0, by decide⟩
      refine ⟨e4 ⟨0, by decide⟩, hα, ?_, ?_⟩
      · exact ggRootClass_of_mem (by simp [GGTwistedTag]) hα
      · intro β hβ
        have hcheck : classOrthB .F4 [[1, 2, 2, 1], [1, 2, 4, 2]] ⟨0, by decide⟩ = true := classOrthB_check_4
        exact stronglyOrth_F4 n f (classOrthB_sound_wrap hcheck β hβ)
  ·
    simp [asClassList] at hL
    rcases hL with rfl | rfl | rfl
    · have hα : e6 ⟨5, by decide⟩ ∈ (ggU .E6 n f).D.roots :=
        e6_mem_roots_E6 n f ⟨5, by decide⟩
      refine ⟨e6 ⟨5, by decide⟩, hα, ?_, ?_⟩
      · exact ggRootClass_of_mem (by simp [GGTwistedTag]) hα
      · intro β hβ
        have hcheck : classOrthB .E6 [[1, 2, 2, 3, 2, 1]] ⟨5, by decide⟩ = true := classOrthB_check_5
        exact stronglyOrth_E6 n f (classOrthB_sound_wrap hcheck β hβ)
    · have hα : e6 ⟨3, by decide⟩ ∈ (ggU .E6 n f).D.roots :=
        e6_mem_roots_E6 n f ⟨3, by decide⟩
      refine ⟨e6 ⟨3, by decide⟩, hα, ?_, ?_⟩
      · exact ggRootClass_of_mem (by simp [GGTwistedTag]) hα
      · intro β hβ
        have hcheck : classOrthB .E6 [[1, 1, 2, 2, 1, 1], [1, 1, 1, 2, 2, 1]] ⟨3, by decide⟩ = true := classOrthB_check_6
        exact stronglyOrth_E6 n f (classOrthB_sound_wrap hcheck β hβ)
    · have hα : e6 ⟨1, by decide⟩ ∈ (ggU .E6 n f).D.roots :=
        e6_mem_roots_E6 n f ⟨1, by decide⟩
      refine ⟨e6 ⟨1, by decide⟩, hα, ?_, ?_⟩
      · exact ggRootClass_of_mem (by simp [GGTwistedTag]) hα
      · intro β hβ
        have hcheck : classOrthB .E6 [[0, 1, 1, 2, 2, 1], [1, 1, 1, 2, 1, 1], [1, 1, 2, 2, 1, 0]] ⟨1, by decide⟩ = true := classOrthB_check_7
        exact stronglyOrth_E6 n f (classOrthB_sound_wrap hcheck β hβ)
  ·
    simp [asClassList] at hL
    rcases hL with rfl | rfl | rfl | rfl | rfl
    · have hα : e7 ⟨6, by decide⟩ ∈ (ggU .E7 n f).D.roots :=
        e7_mem_roots_E7 n f ⟨6, by decide⟩
      refine ⟨e7 ⟨6, by decide⟩, hα, ?_, ?_⟩
      · exact ggRootClass_of_mem (by simp [GGTwistedTag]) hα
      · intro β hβ
        have hcheck : classOrthB .E7 [[2, 2, 3, 4, 3, 2, 1]] ⟨6, by decide⟩ = true := classOrthB_check_8
        exact stronglyOrth_E7 n f (classOrthB_sound_wrap hcheck β hβ)
    · have hα : e7 ⟨6, by decide⟩ ∈ (ggU .E7 n f).D.roots :=
        e7_mem_roots_E7 n f ⟨6, by decide⟩
      refine ⟨e7 ⟨6, by decide⟩, hα, ?_, ?_⟩
      · exact ggRootClass_of_mem (by simp [GGTwistedTag]) hα
      · intro β hβ
        have hcheck : classOrthB .E7 [[1, 1, 2, 3, 3, 2, 1], [1, 2, 2, 3, 2, 2, 1]] ⟨6, by decide⟩ = true := classOrthB_check_9
        exact stronglyOrth_E7 n f (classOrthB_sound_wrap hcheck β hβ)
    · have hα : e7 ⟨4, by decide⟩ ∈ (ggU .E7 n f).D.roots :=
        e7_mem_roots_E7 n f ⟨4, by decide⟩
      refine ⟨e7 ⟨4, by decide⟩, hα, ?_, ?_⟩
      · exact ggRootClass_of_mem (by simp [GGTwistedTag]) hα
      · intro β hβ
        have hcheck : classOrthB .E7 [[1, 2, 2, 3, 2, 1, 0], [1, 1, 2, 2, 2, 2, 1], [1, 1, 2, 3, 2, 1, 1]] ⟨4, by decide⟩ = true := classOrthB_check_10
        exact stronglyOrth_E7 n f (classOrthB_sound_wrap hcheck β hβ)
    · have hα : e7 ⟨3, by decide⟩ ∈ (ggU .E7 n f).D.roots :=
        e7_mem_roots_E7 n f ⟨3, by decide⟩
      refine ⟨e7 ⟨3, by decide⟩, hα, ?_, ?_⟩
      · exact ggRootClass_of_mem (by simp [GGTwistedTag]) hα
      · intro β hβ
        have hcheck : classOrthB .E7 [[1, 1, 1, 2, 2, 1, 1], [1, 1, 2, 2, 1, 1, 1], [0, 1, 1, 2, 2, 2, 1]] ⟨3, by decide⟩ = true := classOrthB_check_11
        exact stronglyOrth_E7 n f (classOrthB_sound_wrap hcheck β hβ)
    · have hα : e7 ⟨3, by decide⟩ ∈ (ggU .E7 n f).D.roots :=
        e7_mem_roots_E7 n f ⟨3, by decide⟩
      refine ⟨e7 ⟨3, by decide⟩, hα, ?_, ?_⟩
      · exact ggRootClass_of_mem (by simp [GGTwistedTag]) hα
      · intro β hβ
        have hcheck : classOrthB .E7 [[1, 2, 2, 3, 2, 1, 0], [0, 1, 1, 2, 2, 2, 1], [1, 1, 2, 2, 1, 1, 1], [1, 1, 1, 2, 2, 1, 1]] ⟨3, by decide⟩ = true := classOrthB_check_12
        exact stronglyOrth_E7 n f (classOrthB_sound_wrap hcheck β hβ)
  ·
    simp [asClassList] at hL
    rcases hL with rfl | rfl | rfl | rfl
    · have hα : e8 ⟨6, by decide⟩ ∈ (ggU .E8 n f).D.roots :=
        e8_mem_roots_E8 n f ⟨6, by decide⟩
      refine ⟨e8 ⟨6, by decide⟩, hα, ?_, ?_⟩
      · exact ggRootClass_of_mem (by simp [GGTwistedTag]) hα
      · intro β hβ
        have hcheck : classOrthB .E8 [[2, 3, 4, 6, 5, 4, 3, 2]] ⟨6, by decide⟩ = true := classOrthB_check_13
        exact stronglyOrth_E8 n f (classOrthB_sound_wrap hcheck β hβ)
    · have hα : e8 ⟨7, by decide⟩ ∈ (ggU .E8 n f).D.roots :=
        e8_mem_roots_E8 n f ⟨7, by decide⟩
      refine ⟨e8 ⟨7, by decide⟩, hα, ?_, ?_⟩
      · exact ggRootClass_of_mem (by simp [GGTwistedTag]) hα
      · intro β hβ
        have hcheck : classOrthB .E8 [[2, 2, 4, 5, 4, 3, 2, 1], [2, 3, 3, 5, 4, 3, 2, 1]] ⟨7, by decide⟩ = true := classOrthB_check_14
        exact stronglyOrth_E8 n f (classOrthB_sound_wrap hcheck β hβ)
    · have hα : e8 ⟨7, by decide⟩ ∈ (ggU .E8 n f).D.roots :=
        e8_mem_roots_E8 n f ⟨7, by decide⟩
      refine ⟨e8 ⟨7, by decide⟩, hα, ?_, ?_⟩
      · exact ggRootClass_of_mem (by simp [GGTwistedTag]) hα
      · intro β hβ
        have hcheck : classOrthB .E8 [[2, 2, 3, 4, 3, 2, 2, 1], [1, 2, 3, 4, 3, 3, 2, 1], [1, 2, 2, 4, 4, 3, 2, 1]] ⟨7, by decide⟩ = true := classOrthB_check_15
        exact stronglyOrth_E8 n f (classOrthB_sound_wrap hcheck β hβ)
    · have hα : e8 ⟨4, by decide⟩ ∈ (ggU .E8 n f).D.roots :=
        e8_mem_roots_E8 n f ⟨4, by decide⟩
      refine ⟨e8 ⟨4, by decide⟩, hα, ?_, ?_⟩
      · exact ggRootClass_of_mem (by simp [GGTwistedTag]) hα
      · intro β hβ
        have hcheck : classOrthB .E8 [[2, 2, 3, 4, 3, 2, 1, 0], [1, 2, 3, 4, 3, 2, 1, 1], [1, 2, 2, 3, 3, 3, 2, 1], [1, 2, 2, 4, 3, 2, 2, 1]] ⟨4, by decide⟩ = true := classOrthB_check_16
        exact stronglyOrth_E8 n f (classOrthB_sound_wrap hcheck β hβ)
  ·
    simp [asClassList] at hL
    rcases hL with rfl | rfl | rfl
    · have hα : e4 ⟨1, by decide⟩ ∈ (ggU .twistedE6 n f).D.roots :=
        e4_mem_roots_twistedE6 n f ⟨1, by decide⟩
      refine ⟨e4 ⟨1, by decide⟩, hα, ?_, ?_⟩
      · exact ⟨hα, fun _ => twistedE6_longRoot_e1 n f⟩
      · intro β hβ
        have hcheck : classOrthB .twistedE6 [[2, 3, 4, 2]] ⟨1, by decide⟩ = true := classOrthB_check_17
        exact stronglyOrth_twistedE6 n f (classOrthB_sound_wrap hcheck β hβ)
    · have hα : e4 ⟨1, by decide⟩ ∈ (ggU .twistedE6 n f).D.roots :=
        e4_mem_roots_twistedE6 n f ⟨1, by decide⟩
      refine ⟨e4 ⟨1, by decide⟩, hα, ?_, ?_⟩
      · exact ⟨hα, fun _ => twistedE6_longRoot_e1 n f⟩
      · intro β hβ
        have hcheck : classOrthB .twistedE6 [[1, 2, 3, 2]] ⟨1, by decide⟩ = true := classOrthB_check_18
        exact stronglyOrth_twistedE6 n f (classOrthB_sound_wrap hcheck β hβ)
    · have hα : e4 ⟨0, by decide⟩ ∈ (ggU .twistedE6 n f).D.roots :=
        e4_mem_roots_twistedE6 n f ⟨0, by decide⟩
      refine ⟨e4 ⟨0, by decide⟩, hα, ?_, ?_⟩
      · exact ⟨hα, fun _ => twistedE6_longRoot_e0 n f⟩
      · intro β hβ
        have hcheck : classOrthB .twistedE6 [[1, 2, 2, 1], [1, 2, 4, 2]] ⟨0, by decide⟩ = true := classOrthB_check_19
        exact stronglyOrth_twistedE6 n f (classOrthB_sound_wrap hcheck β hβ)

end Orth

end CFSG.StandardType
