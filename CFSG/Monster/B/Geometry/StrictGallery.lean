module

public import CFSG.Monster.B.Geometry.ResidueBuilding
public import CFSG.Monster.B.Geometry.CoxeterWords
public import Mathlib.Tactic.ENatToNat

public section

namespace CFSG.Monster.B.Geometry

open CoxeterSystem CFSG.LieType.Chevalley.CosetBuilding CFSG.GroupActions.Exchange

theorem map_altWord {α β : Type*} (f : α → β) (a b : α) (n : ℕ) :
    (altWord a b n).map f = altWord (f a) (f b) n := by
  induction n generalizing a b with
  | zero => rfl
  | succ n ih => simp [ih]

@[expose] def BraidMove.map {B B' : Type*} (f : B → B') (e : BraidMove B) : BraidMove B' :=
  ⟨e.pre.map f, f e.s, f e.t, e.len, e.suf.map f⟩

theorem BraidMove.source_map {B B' : Type*} (f : B → B') (e : BraidMove B) :
    (e.map f).source = e.source.map f := by
  simp [BraidMove.map, BraidMove.source, map_altWord]

theorem BraidMove.target_map {B B' : Type*} (f : B → B') (e : BraidMove B) :
    (e.map f).target = e.target.map f := by
  simp [BraidMove.map, BraidMove.target, map_altWord]

theorem IsBraidPath.map {B B' : Type*} {m : B → B → ℕ} {m' : B' → B' → ℕ} {f : B → B'}
    (hf : ∀ e : BraidMove B, e.IsValid m → (e.map f).IsValid m') {x y : List B}
    {p : List (BraidMove B)} (h : IsBraidPath m x p y) :
    IsBraidPath m' (x.map f) (p.map (BraidMove.map f)) (y.map f) := by
  induction p generalizing x with
  | nil => rw [isBraidPath_nil.mp h]; rfl
  | cons e p ih =>
    obtain ⟨he, rfl, hp⟩ := h
    refine ⟨hf e he, BraidMove.source_map f e, ?_⟩
    rw [BraidMove.target_map]
    exact ih hp

section Coxeter

variable {ι : Type*} {M : CoxeterMatrix ι} {W : Type*} [Group W] (cs : CoxeterSystem M W)

@[expose] noncomputable def braidExponent (i j : ι) : ℕ := orderOf (cs.simple i * cs.simple j)

variable {cs}

theorem braidExponent_eq (i j : ι) : braidExponent cs i j = M i j :=
  cs.orderOf_simple_mul_simple i j

theorem braidExponent_comm (i j : ι) : braidExponent cs i j = braidExponent cs j i := by
  rw [braidExponent_eq, braidExponent_eq, M.symmetric]

theorem altWord_eq_reverse_alternatingWord (a b : ι) (n : ℕ) :
    altWord a b n = (alternatingWord b a n).reverse := by
  induction n generalizing a b with
  | zero => rfl
  | succ n ih => simp [ih b a, alternatingWord_succ]

theorem isReduced_altWord {s t : ι} (hst : s ≠ t) (hM : M s t ≠ 0) :
    cs.IsReduced (altWord s t (M s t)) := by
  rw [altWord_eq_reverse_alternatingWord]
  have h : cs.IsReduced (alternatingWord t s (M t s)) :=
    (isLongest_braidWord (cs := cs) hst.symm (by rwa [M.symmetric])).2.1
  rw [M.symmetric t s] at h
  exact h.reverse

theorem wordProd_altWord_comm (s t : ι) :
    cs.wordProd (altWord s t (M s t)) = cs.wordProd (altWord t s (M s t)) := by
  rw [altWord_eq_reverse_alternatingWord, altWord_eq_reverse_alternatingWord, cs.wordProd_reverse,
    cs.wordProd_reverse]
  have h : cs.wordProd (alternatingWord t s (M t s)) =
      cs.wordProd (alternatingWord s t (M s t)) := cs.wordProd_braidWord_eq t s
  rw [M.symmetric t s] at h
  rw [h]

theorem BraidMove.wordProd_target_of_isValid {e : BraidMove ι}
    (he : e.IsValid (braidExponent cs)) : cs.wordProd e.target = cs.wordProd e.source := by
  have hlen : e.len = M e.s e.t := he.2.1.trans (braidExponent_eq _ _)
  simp only [BraidMove.target, BraidMove.source, cs.wordProd_append, hlen,
    wordProd_altWord_comm e.s e.t]

theorem IsBraidPath.wordProd_eq_of_braidExponent {x y : List ι} {p : List (BraidMove ι)}
    (h : IsBraidPath (braidExponent cs) x p y) : cs.wordProd y = cs.wordProd x :=
  h.apply_eq cs.wordProd fun _ he => BraidMove.wordProd_target_of_isValid he

theorem IsBraidPath.isReduced_of_braidExponent {x y : List ι} {p : List (BraidMove ι)}
    (h : IsBraidPath (braidExponent cs) x p y) (hx : cs.IsReduced x) : cs.IsReduced y := by
  rw [CoxeterSystem.IsReduced, h.wordProd_eq_of_braidExponent, h.length_eq]
  exact hx

noncomputable def simpleIndex (s : simpleSet cs) : ι := s.2.choose

theorem simple_simpleIndex (s : simpleSet cs) : cs.simple (simpleIndex s) = s :=
  s.2.choose_spec

theorem simpleIndex_mk (i : ι) : simpleIndex (⟨cs.simple i, i, rfl⟩ : simpleSet cs) = i :=
  cs.simple_injective (simple_simpleIndex _)

theorem map_simpleIndex_toSWord (ω : List ι) : (toSWord cs ω).map simpleIndex = ω := by
  simp [toSWord, Function.comp_def, simpleIndex_mk]

theorem exists_isBraidPath_index {x y : List ι} (hx : cs.IsReduced x) (hy : cs.IsReduced y)
    (hxy : cs.wordProd x = cs.wordProd y) :
    ∃ p, IsBraidPath (braidExponent cs) x p y := by
  obtain ⟨γ, hγ⟩ := exists_isBraidPath orderOf_simpleSet exchangeCondition_simpleSet
    (isReduced_toSWord_iff.mpr hx) (isReduced_toSWord_iff.mpr hy)
    (by rw [wordProd_toSWord, wordProd_toSWord, hxy])
  refine ⟨γ.map (BraidMove.map simpleIndex), ?_⟩
  have h := hγ.map (m' := braidExponent cs) (f := simpleIndex) fun e he => by
    refine ⟨fun h => he.1 (Subtype.ext ?_), ?_, he.2.2⟩
    · rw [← simple_simpleIndex e.s, ← simple_simpleIndex e.t]
      exact congrArg cs.simple h
    · refine he.2.1.trans ?_
      change orderOf ((e.s : W) * e.t) = orderOf (cs.simple (simpleIndex e.s) *
        cs.simple (simpleIndex e.t))
      rw [simple_simpleIndex, simple_simpleIndex]
  rwa [map_simpleIndex_toSWord, map_simpleIndex_toSWord] at h

end Coxeter

namespace ChamberSystem

variable {ι : Type*} {M : CoxeterMatrix ι} {W : Type*} [Group W] {cs : CoxeterSystem M W}
variable {C : Type*}

variable (X : ChamberSystem ι C) in
@[expose] def IsOrdinary : C → List (ι × C) → Prop
  | _, [] => True
  | x, p :: γ => X.adj p.1 x p.2 ∧ x ≠ p.2 ∧ IsOrdinary p.2 γ

variable (X : ChamberSystem ι C) (cs) in
@[expose] def IsReducedOrdinary (x : C) (γ : List (ι × C)) : Prop :=
  X.IsOrdinary x γ ∧ cs.IsReduced (galleryType γ)

variable {X : ChamberSystem ι C}

@[simp] theorem isOrdinary_nil (x : C) : X.IsOrdinary x [] := trivial

@[simp] theorem isOrdinary_cons (x : C) (p : ι × C) (γ : List (ι × C)) :
    X.IsOrdinary x (p :: γ) ↔ X.adj p.1 x p.2 ∧ x ≠ p.2 ∧ X.IsOrdinary p.2 γ :=
  Iff.rfl

theorem isOrdinary_append (x : C) (γ η : List (ι × C)) :
    X.IsOrdinary x (γ ++ η) ↔ X.IsOrdinary x γ ∧ X.IsOrdinary (galleryEnd x γ) η := by
  induction γ generalizing x with
  | nil => simp
  | cons p γ ih => simp [ih, and_assoc]

theorem isOrdinary_concat (x : C) (γ : List (ι × C)) (p : ι × C) :
    X.IsOrdinary x (γ ++ [p]) ↔
      X.IsOrdinary x γ ∧ X.adj p.1 (galleryEnd x γ) p.2 ∧ galleryEnd x γ ≠ p.2 := by
  simp [isOrdinary_append]

theorem IsOrdinary.isGallery {x : C} {γ : List (ι × C)} (h : X.IsOrdinary x γ) :
    X.IsGallery x γ := by
  induction γ generalizing x with
  | nil => trivial
  | cons p γ ih => exact ⟨h.1, ih h.2.2⟩

theorem IsReducedOrdinary.nil (x : C) : X.IsReducedOrdinary cs x [] :=
  ⟨trivial, by simp [CoxeterSystem.IsReduced]⟩

section ResidueBuilding

variable {J : Set ι} {x : C} {δ : C → C → W}
  (hB : IsBuildingOn cs δ J (X.residue J x))
  (hadj : ∀ y ∈ X.residue J x, ∀ z ∈ X.residue J x, ∀ j ∈ J,
    (X.adj j y z ↔ δ y z = 1 ∨ δ y z = cs.simple j))
include hB hadj

theorem isOrdinary_iff_isStrictGallery {y : C} (hy : y ∈ X.residue J x) {η : List (ι × C)}
    (hJ : ∀ i ∈ galleryType η, i ∈ J) :
    X.IsOrdinary y η ↔ IsStrictGallery cs δ y η ∧ ∀ p ∈ η, p.2 ∈ X.residue J x := by
  induction η generalizing y with
  | nil => simp
  | cons p η ih =>
    have hp : p.1 ∈ J := hJ p.1 (by simp)
    have hJ' : ∀ i ∈ galleryType η, i ∈ J := fun i hi => hJ i (by simp [hi])
    constructor
    · rintro ⟨h1, h2, h3⟩
      have hpR : p.2 ∈ X.residue J x := mem_residue_trans hy
        (residue_mono (Set.singleton_subset_iff.mpr hp) y (mem_residue_singleton.mpr h1))
      obtain ⟨ih1, ih2⟩ := (ih hpR hJ').mp h3
      have hδ : δ y p.2 = cs.simple p.1 := by
        rcases (hadj y hy p.2 hpR p.1 hp).mp h1 with h | h
        · exact absurd ((hB.eq_one_iff y hy p.2 hpR).mp h) h2
        · exact h
      refine ⟨⟨hδ, ih1⟩, fun q hq => ?_⟩
      rcases List.mem_cons.mp hq with rfl | hq
      · exact hpR
      · exact ih2 q hq
    · rintro ⟨⟨h1, h2⟩, h3⟩
      have hpR : p.2 ∈ X.residue J x := h3 p (by simp)
      refine ⟨(hadj y hy p.2 hpR p.1 hp).mpr (Or.inr h1), fun h => ?_,
        (ih hpR hJ').mpr ⟨h2, fun q hq => h3 q (by simp [hq])⟩⟩
      rw [← h, hB.eq_one_self hy] at h1
      exact cs.simple_ne_one _ h1.symm

theorem eq_of_isOrdinary_of_isBuildingOn {y : C} (hy : y ∈ X.residue J x) {η η' : List (ι × C)}
    (hη : X.IsOrdinary y η) (hη' : X.IsOrdinary y η') (hJ : ∀ i ∈ galleryType η, i ∈ J)
    (htype : galleryType η = galleryType η') (hred : cs.IsReduced (galleryType η))
    (hend : galleryEnd y η = galleryEnd y η') : η = η' := by
  have hJ' : ∀ i ∈ galleryType η', i ∈ J := htype ▸ hJ
  obtain ⟨h1, h2⟩ := (isOrdinary_iff_isStrictGallery hB hadj hy hJ).mp hη
  obtain ⟨h1', h2'⟩ := (isOrdinary_iff_isStrictGallery hB hadj hy hJ').mp hη'
  exact hB.eq_of_isStrictGallery hy h1 h1' h2 h2' hJ htype hred hend

theorem exists_isOrdinary_of_isBuildingOn {y z : C} (hy : y ∈ X.residue J x)
    (hz : z ∈ X.residue J x) {ω : List ι} (hω : cs.IsReduced ω) (h : cs.wordProd ω = δ y z) :
    ∃ η, X.IsOrdinary y η ∧ galleryType η = ω ∧ galleryEnd y η = z := by
  obtain ⟨η, hη, htype, hend, hR⟩ := hB.exists_strictGallery hy hz hω h
  have hJ : ∀ i ∈ galleryType η, i ∈ J := by
    rw [htype]
    intro i hi
    exact mem_of_isReduced_of_mem_parabolic cs hω (h ▸ hB.mem_parabolic y hy z hz) hi
  exact ⟨η, (isOrdinary_iff_isStrictGallery hB hadj hy hJ).mpr ⟨hη, hR⟩, htype, hend⟩

theorem dist_eq_of_isOrdinary {y : C} (hy : y ∈ X.residue J x) {η : List (ι × C)}
    (hη : X.IsOrdinary y η) (hJ : ∀ i ∈ galleryType η, i ∈ J)
    (hred : cs.IsReduced (galleryType η)) :
    δ y (galleryEnd y η) = cs.wordProd (galleryType η) := by
  obtain ⟨h1, h2⟩ := (isOrdinary_iff_isStrictGallery hB hadj hy hJ).mp hη
  exact hB.dist_eq hy h1 h2 hJ hred

end ResidueBuilding

theorem IsResidueBuilding.eq_of_isReducedOrdinary {J : Set ι} {x : C}
    (h : X.IsResidueBuilding cs J x) {η η' : List (ι × C)} (hη : X.IsReducedOrdinary cs x η)
    (hη' : X.IsOrdinary x η') (hJ : ∀ i ∈ galleryType η, i ∈ J)
    (htype : galleryType η = galleryType η') (hend : galleryEnd x η = galleryEnd x η') :
    η = η' := by
  obtain ⟨δ, hB, hadj⟩ := h
  exact eq_of_isOrdinary_of_isBuildingOn hB hadj (X.self_mem_residue J x) hη.1 hη' hJ htype hη.2
    hend

variable (X : ChamberSystem ι C) in
@[expose] def IsStrictMoveAt (x : C) (e : BraidMove ι) (γ γ' : List (ι × C)) : Prop :=
  ∃ γ₁ η η' γ₂ : List (ι × C), γ = γ₁ ++ η ++ γ₂ ∧ γ' = γ₁ ++ η' ++ γ₂ ∧
    galleryType γ₁ = e.pre ∧ galleryType η = altWord e.s e.t e.len ∧
    galleryType η' = altWord e.t e.s e.len ∧ galleryType γ₂ = e.suf ∧
    X.IsOrdinary (galleryEnd x γ₁) η ∧ X.IsOrdinary (galleryEnd x γ₁) η' ∧
    galleryEnd (galleryEnd x γ₁) η = galleryEnd (galleryEnd x γ₁) η'

variable (X : ChamberSystem ι C) (cs) in
@[expose] def StrictMove (x : C) (γ γ' : List (ι × C)) : Prop :=
  ∃ e : BraidMove ι, e.IsValid (braidExponent cs) ∧ X.IsStrictMoveAt x e γ γ'

variable (X : ChamberSystem ι C) (cs) in
@[expose] def StrictHomotopic (x : C) : List (ι × C) → List (ι × C) → Prop :=
  Relation.EqvGen (X.StrictMove cs x)

namespace IsStrictMoveAt

variable {x : C} {e : BraidMove ι} {γ γ' : List (ι × C)}

theorem reverse (h : X.IsStrictMoveAt x e γ γ') : X.IsStrictMoveAt x e.reverse γ' γ := by
  obtain ⟨γ₁, η, η', γ₂, rfl, rfl, h1, h2, h3, h4, h5, h6, h7⟩ := h
  exact ⟨γ₁, η', η, γ₂, rfl, rfl, h1, h3, h2, h4, h6, h5, h7.symm⟩

theorem galleryType_eq (h : X.IsStrictMoveAt x e γ γ') :
    galleryType γ = e.source ∧ galleryType γ' = e.target := by
  obtain ⟨γ₁, η, η', γ₂, rfl, rfl, h1, h2, h3, h4, -⟩ := h
  simp [BraidMove.source, BraidMove.target, h1, h2, h3, h4]

theorem galleryEnd_eq (h : X.IsStrictMoveAt x e γ γ') : galleryEnd x γ = galleryEnd x γ' := by
  obtain ⟨γ₁, η, η', γ₂, rfl, rfl, -, -, -, -, -, -, h7⟩ := h
  simp only [galleryEnd_append, h7]

theorem length_eq (h : X.IsStrictMoveAt x e γ γ') : γ'.length = γ.length := by
  obtain ⟨γ₁, η, η', γ₂, rfl, rfl, -, h2, h3, -⟩ := h
  have e2 := congrArg List.length h2
  have e3 := congrArg List.length h3
  simp only [length_galleryType, length_altWord] at e2 e3
  simp [e2, e3]

theorem isOrdinary_iff (h : X.IsStrictMoveAt x e γ γ') :
    X.IsOrdinary x γ ↔ X.IsOrdinary x γ' := by
  obtain ⟨γ₁, η, η', γ₂, rfl, rfl, -, -, -, -, h5, h6, h7⟩ := h
  simp only [isOrdinary_append, galleryEnd_append, h7]
  tauto

theorem elemMove (h : X.IsStrictMoveAt x e γ γ') : X.ElemMove x γ γ' := by
  obtain ⟨γ₁, η, η', γ₂, rfl, rfl, -, h2, h3, -, h5, h6, h7⟩ := h
  have hJ : ({e.s, e.t} : Set ι).encard ≤ 2 :=
    (Set.encard_insert_le _ _).trans (by rw [Set.encard_singleton]; norm_num)
  refine .mk γ₁ η η' γ₂ {e.s, e.t} hJ h5.isGallery h6.isGallery (fun i hi => ?_)
    (fun i hi => ?_) h7
  · rw [h2] at hi
    rcases mem_altWord hi with rfl | rfl <;> simp
  · rw [h3] at hi
    rcases mem_altWord hi with rfl | rfl <;> simp

theorem append_right (h : X.IsStrictMoveAt x e γ γ') (δ : List (ι × C)) :
    X.IsStrictMoveAt x (e.extend [] (galleryType δ)) (γ ++ δ) (γ' ++ δ) := by
  obtain ⟨γ₁, η, η', γ₂, rfl, rfl, h1, h2, h3, h4, h5, h6, h7⟩ := h
  exact ⟨γ₁, η, η', γ₂ ++ δ, by simp, by simp, by simpa [BraidMove.extend] using h1, h2, h3,
    by simp [BraidMove.extend, h4], h5, h6, h7⟩

theorem append_left (α : List (ι × C)) (h : X.IsStrictMoveAt (galleryEnd x α) e γ γ') :
    X.IsStrictMoveAt x (e.extend (galleryType α) []) (α ++ γ) (α ++ γ') := by
  obtain ⟨γ₁, η, η', γ₂, rfl, rfl, h1, h2, h3, h4, h5, h6, h7⟩ := h
  refine ⟨α ++ γ₁, η, η', γ₂, by simp, by simp, by simp [BraidMove.extend, h1], h2, h3,
    by simp [BraidMove.extend, h4], ?_, ?_, ?_⟩ <;> rw [galleryEnd_append]
  · exact h5
  · exact h6
  · exact h7

end IsStrictMoveAt

theorem exists_split_of_galleryType_eq_append {γ : List (ι × C)} {a b : List ι}
    (h : galleryType γ = a ++ b) :
    ∃ γ₁ γ₂, γ = γ₁ ++ γ₂ ∧ galleryType γ₁ = a ∧ galleryType γ₂ = b :=
  List.map_eq_append_iff.mp h

section Moves

variable (hres : ∀ s t : ι, s ≠ t → ∀ y : C, X.IsResidueBuilding cs {s, t} y)
include hres

theorem exists_isStrictMoveAt {x : C} {e : BraidMove ι} (he : e.IsValid (braidExponent cs))
    {γ : List (ι × C)} (hγ : X.IsOrdinary x γ) (htype : galleryType γ = e.source) :
    ∃ γ', X.IsStrictMoveAt x e γ γ' := by
  obtain ⟨hst, hlen, hne⟩ := he
  rw [braidExponent_eq] at hlen
  have hM : M e.s e.t ≠ 0 := hlen ▸ hne
  obtain ⟨γ₁₂, γ₂, rfl, h12, h2⟩ := exists_split_of_galleryType_eq_append htype
  obtain ⟨γ₁, η, rfl, h1, hη⟩ := exists_split_of_galleryType_eq_append h12
  rw [isOrdinary_append, isOrdinary_append] at hγ
  obtain ⟨⟨-, hηo⟩, hγ₂⟩ := hγ
  obtain ⟨δ, hB, hadj⟩ := hres e.s e.t hst (galleryEnd x γ₁)
  have hy := X.self_mem_residue {e.s, e.t} (galleryEnd x γ₁)
  have hJ : ∀ i ∈ galleryType η, i ∈ ({e.s, e.t} : Set ι) := fun i hi => by
    rw [hη] at hi
    rcases mem_altWord hi with rfl | rfl <;> simp
  have hred : cs.IsReduced (galleryType η) := by rw [hη, hlen]; exact isReduced_altWord hst hM
  have hdist := dist_eq_of_isOrdinary hB hadj hy hηo hJ hred
  have hredt : cs.IsReduced (altWord e.t e.s e.len) := by
    have := isReduced_altWord (cs := cs) hst.symm (by rwa [M.symmetric])
    rwa [M.symmetric, ← hlen] at this
  have hprod : cs.wordProd (altWord e.t e.s e.len) =
      δ (galleryEnd x γ₁) (galleryEnd (galleryEnd x γ₁) η) := by
    rw [hdist, hη, hlen, wordProd_altWord_comm]
  obtain ⟨η', hη'o, hη't, hη'e⟩ := exists_isOrdinary_of_isBuildingOn hB hadj hy
    (galleryEnd_mem_residue hηo.isGallery hJ) hredt hprod
  exact ⟨γ₁ ++ η' ++ γ₂, γ₁, η, η', γ₂, rfl, rfl, h1, hη, hη't, h2, hηo, hη'o, hη'e.symm⟩

theorem IsStrictMoveAt.unique {x : C} {e : BraidMove ι} (he : e.IsValid (braidExponent cs))
    {γ γ' γ'' : List (ι × C)} (h : X.IsStrictMoveAt x e γ γ')
    (h' : X.IsStrictMoveAt x e γ γ'') : γ' = γ'' := by
  obtain ⟨hst, hlen, hne⟩ := he
  rw [braidExponent_eq] at hlen
  have hM : M e.s e.t ≠ 0 := hlen ▸ hne
  obtain ⟨γ₁, η, η', γ₂, rfl, rfl, h1, h2, h3, h4, h5, h6, h7⟩ := h
  obtain ⟨ζ₁, ζ, ζ', ζ₂, hζ, rfl, k1, k2, k3, k4, k5, k6, k7⟩ := h'
  have l1 : γ₁.length = ζ₁.length := by
    rw [← length_galleryType, ← length_galleryType, h1, k1]
  have l2 : η.length = ζ.length := by
    rw [← length_galleryType, ← length_galleryType, h2, k2]
  obtain ⟨e12, rfl⟩ := List.append_inj hζ (by simp [l1, l2])
  obtain ⟨rfl, rfl⟩ := List.append_inj e12 l1
  obtain ⟨δ, hB, hadj⟩ := hres e.s e.t hst (galleryEnd x γ₁)
  have hy := X.self_mem_residue {e.s, e.t} (galleryEnd x γ₁)
  have hJ : ∀ i ∈ galleryType η', i ∈ ({e.s, e.t} : Set ι) := fun i hi => by
    rw [h3] at hi
    rcases mem_altWord hi with rfl | rfl <;> simp
  have hredt : cs.IsReduced (galleryType η') := by
    have := isReduced_altWord (cs := cs) hst.symm (by rwa [M.symmetric])
    rw [h3, hlen, M.symmetric e.s e.t]
    exact this
  have : η' = ζ' := eq_of_isOrdinary_of_isBuildingOn hB hadj hy h6 k6 hJ (h3.trans k3.symm) hredt
    (h7.symm.trans k7)
  rw [this]

end Moves

namespace StrictMove

variable {x : C} {γ γ' : List (ι × C)}

theorem symm (h : X.StrictMove cs x γ γ') : X.StrictMove cs x γ' γ := by
  obtain ⟨e, he, h⟩ := h
  exact ⟨e.reverse, he.reverse braidExponent_comm, h.reverse⟩

theorem galleryEnd_eq (h : X.StrictMove cs x γ γ') : galleryEnd x γ = galleryEnd x γ' := by
  obtain ⟨e, -, h⟩ := h
  exact h.galleryEnd_eq

theorem isOrdinary_iff (h : X.StrictMove cs x γ γ') : X.IsOrdinary x γ ↔ X.IsOrdinary x γ' := by
  obtain ⟨e, -, h⟩ := h
  exact h.isOrdinary_iff

theorem wordProd_eq (h : X.StrictMove cs x γ γ') :
    cs.wordProd (galleryType γ') = cs.wordProd (galleryType γ) := by
  obtain ⟨e, he, h⟩ := h
  rw [h.galleryType_eq.1, h.galleryType_eq.2]
  exact BraidMove.wordProd_target_of_isValid he

theorem length_eq (h : X.StrictMove cs x γ γ') : γ'.length = γ.length := by
  obtain ⟨e, -, h⟩ := h
  exact h.length_eq

theorem isReducedOrdinary_iff (h : X.StrictMove cs x γ γ') :
    X.IsReducedOrdinary cs x γ ↔ X.IsReducedOrdinary cs x γ' := by
  have hp := h.wordProd_eq
  have hl := h.length_eq
  rw [IsReducedOrdinary, IsReducedOrdinary, h.isOrdinary_iff, CoxeterSystem.IsReduced,
    CoxeterSystem.IsReduced, hp, length_galleryType, length_galleryType, hl]

theorem elemMove (h : X.StrictMove cs x γ γ') : X.ElemMove x γ γ' := by
  obtain ⟨e, -, h⟩ := h
  exact h.elemMove

theorem append_right (h : X.StrictMove cs x γ γ') (δ : List (ι × C)) :
    X.StrictMove cs x (γ ++ δ) (γ' ++ δ) := by
  obtain ⟨e, he, h⟩ := h
  exact ⟨_, he.extend [] _, h.append_right δ⟩

theorem append_left (α : List (ι × C)) (h : X.StrictMove cs (galleryEnd x α) γ γ') :
    X.StrictMove cs x (α ++ γ) (α ++ γ') := by
  obtain ⟨e, he, h⟩ := h
  exact ⟨_, he.extend _ [], h.append_left α⟩

end StrictMove

namespace StrictHomotopic

variable {x : C} {γ γ' γ'' : List (ι × C)}

@[refl] protected theorem refl (γ : List (ι × C)) : X.StrictHomotopic cs x γ γ :=
  Relation.EqvGen.refl γ

@[symm] protected theorem symm (h : X.StrictHomotopic cs x γ γ') : X.StrictHomotopic cs x γ' γ :=
  Relation.EqvGen.symm _ _ h

@[trans] protected theorem trans (h : X.StrictHomotopic cs x γ γ')
    (h' : X.StrictHomotopic cs x γ' γ'') : X.StrictHomotopic cs x γ γ'' :=
  Relation.EqvGen.trans _ _ _ h h'

theorem of_strictMove (h : X.StrictMove cs x γ γ') : X.StrictHomotopic cs x γ γ' :=
  Relation.EqvGen.rel _ _ h

theorem of_reflTransGen (h : Relation.ReflTransGen (X.StrictMove cs x) γ γ') :
    X.StrictHomotopic cs x γ γ' := by
  induction h with
  | refl => rfl
  | tail _ h ih => exact ih.trans (of_strictMove h)

theorem iff_reflTransGen :
    X.StrictHomotopic cs x γ γ' ↔ Relation.ReflTransGen (X.StrictMove cs x) γ γ' := by
  refine ⟨fun h => ?_, of_reflTransGen⟩
  induction h with
  | rel _ _ h => exact .single h
  | refl => exact .refl
  | symm _ _ _ ih =>
    clear * - ih
    induction ih with
    | refl => exact .refl
    | tail _ h ih => exact Relation.ReflTransGen.head h.symm ih
  | trans _ _ _ _ _ ih ih' => exact ih.trans ih'

theorem induction_on {P : List (ι × C) → List (ι × C) → Prop} (refl : ∀ γ, P γ γ)
    (symm : ∀ γ γ', P γ γ' → P γ' γ) (trans : ∀ γ γ' γ'', P γ γ' → P γ' γ'' → P γ γ'')
    (step : ∀ γ γ', X.StrictMove cs x γ γ' → P γ γ') (h : X.StrictHomotopic cs x γ γ') :
    P γ γ' := by
  induction h with
  | rel _ _ h => exact step _ _ h
  | refl => exact refl _
  | symm _ _ _ ih => exact symm _ _ ih
  | trans _ _ _ _ _ ih ih' => exact trans _ _ _ ih ih'

theorem galleryEnd_eq (h : X.StrictHomotopic cs x γ γ') : galleryEnd x γ = galleryEnd x γ' :=
  h.induction_on (P := fun γ γ' => galleryEnd x γ = galleryEnd x γ') (fun _ => rfl)
    (fun _ _ h => h.symm) (fun _ _ _ h h' => h.trans h') fun _ _ h => h.galleryEnd_eq

theorem isOrdinary_iff (h : X.StrictHomotopic cs x γ γ') :
    X.IsOrdinary x γ ↔ X.IsOrdinary x γ' :=
  h.induction_on (P := fun γ γ' => X.IsOrdinary x γ ↔ X.IsOrdinary x γ') (fun _ => Iff.rfl)
    (fun _ _ h => h.symm) (fun _ _ _ h h' => h.trans h') fun _ _ h => h.isOrdinary_iff

theorem isReducedOrdinary_iff (h : X.StrictHomotopic cs x γ γ') :
    X.IsReducedOrdinary cs x γ ↔ X.IsReducedOrdinary cs x γ' :=
  h.induction_on (P := fun γ γ' => X.IsReducedOrdinary cs x γ ↔ X.IsReducedOrdinary cs x γ')
    (fun _ => Iff.rfl) (fun _ _ h => h.symm) (fun _ _ _ h h' => h.trans h')
    fun _ _ h => h.isReducedOrdinary_iff

theorem wordProd_eq (h : X.StrictHomotopic cs x γ γ') :
    cs.wordProd (galleryType γ) = cs.wordProd (galleryType γ') :=
  h.induction_on (P := fun γ γ' => cs.wordProd (galleryType γ) = cs.wordProd (galleryType γ'))
    (fun _ => rfl) (fun _ _ h => h.symm) (fun _ _ _ h h' => h.trans h')
    fun _ _ h => h.wordProd_eq.symm

theorem length_eq (h : X.StrictHomotopic cs x γ γ') : γ.length = γ'.length :=
  h.induction_on (P := fun γ γ' => γ.length = γ'.length) (fun _ => rfl) (fun _ _ h => h.symm)
    (fun _ _ _ h h' => h.trans h') fun _ _ h => h.length_eq.symm

theorem twoHomotopic (h : X.StrictHomotopic cs x γ γ') : X.TwoHomotopic x γ γ' :=
  h.induction_on (P := fun γ γ' => X.TwoHomotopic x γ γ') (fun _ => .refl _)
    (fun _ _ h => h.symm) (fun _ _ _ h h' => h.trans h') fun _ _ h => .of_elemMove h.elemMove

theorem append_right (h : X.StrictHomotopic cs x γ γ') (δ : List (ι × C)) :
    X.StrictHomotopic cs x (γ ++ δ) (γ' ++ δ) :=
  h.induction_on (P := fun γ γ' => X.StrictHomotopic cs x (γ ++ δ) (γ' ++ δ))
    (fun _ => .refl _)
    (fun _ _ h => h.symm) (fun _ _ _ h h' => h.trans h')
    fun _ _ h => of_strictMove (h.append_right δ)

theorem append_left (α : List (ι × C)) (h : X.StrictHomotopic cs (galleryEnd x α) γ γ') :
    X.StrictHomotopic cs x (α ++ γ) (α ++ γ') :=
  h.induction_on (P := fun γ γ' => X.StrictHomotopic cs x (α ++ γ) (α ++ γ'))
    (fun _ => .refl _)
    (fun _ _ h => h.symm) (fun _ _ _ h h' => h.trans h')
    fun _ _ h => of_strictMove (h.append_left α)

end StrictHomotopic

variable (X : ChamberSystem ι C) in
@[expose] def IsStrictLift (x : C) : List (BraidMove ι) → List (ι × C) → List (ι × C) → Prop
  | [], γ, γ' => γ = γ'
  | e :: p, γ, γ' => ∃ γ₁, X.IsStrictMoveAt x e γ γ₁ ∧ IsStrictLift x p γ₁ γ'

@[simp] theorem isStrictLift_nil {x : C} {γ γ' : List (ι × C)} :
    X.IsStrictLift x [] γ γ' ↔ γ = γ' :=
  Iff.rfl

theorem isStrictLift_cons {x : C} {e : BraidMove ι} {p : List (BraidMove ι)}
    {γ γ' : List (ι × C)} :
    X.IsStrictLift x (e :: p) γ γ' ↔ ∃ γ₁, X.IsStrictMoveAt x e γ γ₁ ∧ X.IsStrictLift x p γ₁ γ' :=
  Iff.rfl

theorem isStrictLift_append {x : C} {p q : List (BraidMove ι)} {γ γ' : List (ι × C)} :
    X.IsStrictLift x (p ++ q) γ γ' ↔ ∃ γ₁, X.IsStrictLift x p γ γ₁ ∧ X.IsStrictLift x q γ₁ γ' := by
  induction p generalizing γ with
  | nil => simp
  | cons e p ih =>
    simp only [List.cons_append, isStrictLift_cons, ih]
    exact ⟨fun ⟨γ₁, h1, γ₂, h2, h3⟩ => ⟨γ₂, ⟨γ₁, h1, h2⟩, h3⟩,
      fun ⟨γ₂, ⟨γ₁, h1, h2⟩, h3⟩ => ⟨γ₁, h1, γ₂, h2, h3⟩⟩

namespace IsStrictLift

variable {x : C} {p : List (BraidMove ι)} {γ γ' : List (ι × C)}

theorem galleryEnd_eq (h : X.IsStrictLift x p γ γ') : galleryEnd x γ = galleryEnd x γ' := by
  induction p generalizing γ with
  | nil => exact congrArg _ h
  | cons e p ih =>
    obtain ⟨γ₁, h1, h2⟩ := h
    exact h1.galleryEnd_eq.trans (ih h2)

theorem isOrdinary_iff (h : X.IsStrictLift x p γ γ') : X.IsOrdinary x γ ↔ X.IsOrdinary x γ' := by
  induction p generalizing γ with
  | nil => rw [isStrictLift_nil.mp h]
  | cons e p ih =>
    obtain ⟨γ₁, h1, h2⟩ := h
    exact h1.isOrdinary_iff.trans (ih h2)

theorem strictHomotopic (hp : ∀ e ∈ p, e.IsValid (braidExponent cs))
    (h : X.IsStrictLift x p γ γ') : X.StrictHomotopic cs x γ γ' := by
  induction p generalizing γ with
  | nil => rw [isStrictLift_nil.mp h]
  | cons e p ih =>
    obtain ⟨γ₁, h1, h2⟩ := h
    exact (StrictHomotopic.of_strictMove ⟨e, hp e (by simp), h1⟩).trans
      (ih (fun e' he' => hp e' (by simp [he'])) h2)

theorem unique (hres : ∀ s t : ι, s ≠ t → ∀ y : C, X.IsResidueBuilding cs {s, t} y)
    (hp : ∀ e ∈ p, e.IsValid (braidExponent cs)) {γ'' : List (ι × C)}
    (h : X.IsStrictLift x p γ γ') (h' : X.IsStrictLift x p γ γ'') : γ' = γ'' := by
  induction p generalizing γ with
  | nil => exact (isStrictLift_nil.mp h).symm.trans (isStrictLift_nil.mp h')
  | cons e p ih =>
    obtain ⟨γ₁, h1, h2⟩ := h
    obtain ⟨γ₂, k1, k2⟩ := h'
    obtain rfl := h1.unique hres (hp e (by simp)) k1
    exact ih (fun e' he' => hp e' (by simp [he'])) h2 k2

end IsStrictLift

theorem exists_isStrictLift (hres : ∀ s t : ι, s ≠ t → ∀ y : C, X.IsResidueBuilding cs {s, t} y)
    {x : C} {p : List (BraidMove ι)} {ω ω' : List ι} (hp : IsBraidPath (braidExponent cs) ω p ω')
    {γ : List (ι × C)} (hγ : X.IsOrdinary x γ) (htype : galleryType γ = ω) :
    ∃ γ', X.IsStrictLift x p γ γ' ∧ X.IsOrdinary x γ' ∧ galleryType γ' = ω' ∧
      galleryEnd x γ' = galleryEnd x γ := by
  induction p generalizing γ ω with
  | nil => exact ⟨γ, rfl, hγ, htype.trans (isBraidPath_nil.mp hp), rfl⟩
  | cons e p ih =>
    obtain ⟨he, hsrc, hp⟩ := hp
    obtain ⟨γ₁, h1⟩ := exists_isStrictMoveAt hres he hγ (htype.trans hsrc.symm)
    obtain ⟨γ', h2, h3, h4, h5⟩ := ih hp (h1.isOrdinary_iff.mp hγ) h1.galleryType_eq.2
    exact ⟨γ', ⟨γ₁, h1, h2⟩, h3, h4, h5.trans h1.galleryEnd_eq.symm⟩

theorem exists_strictHomotopic_of_isReduced
    (hres : ∀ s t : ι, s ≠ t → ∀ y : C, X.IsResidueBuilding cs {s, t} y) {x : C}
    {γ : List (ι × C)} (hγ : X.IsReducedOrdinary cs x γ) {ω : List ι} (hω : cs.IsReduced ω)
    (h : cs.wordProd ω = cs.wordProd (galleryType γ)) :
    ∃ γ', X.StrictHomotopic cs x γ γ' ∧ X.IsReducedOrdinary cs x γ' ∧ galleryType γ' = ω := by
  obtain ⟨p, hp⟩ := exists_isBraidPath_index hγ.2 hω h.symm
  obtain ⟨γ', h1, h2, h3, -⟩ := exists_isStrictLift hres hp hγ.1 rfl
  exact ⟨γ', h1.strictHomotopic fun e he => hp.isValid_of_mem he, ⟨h2, h3 ▸ hω⟩, h3⟩

@[expose] def ConstantDeletion (x : C) (γ γ' : List (ι × C)) : Prop :=
  ∃ (γ₁ γ₂ : List (ι × C)) (i : ι), γ = γ₁ ++ [(i, galleryEnd x γ₁)] ++ γ₂ ∧ γ' = γ₁ ++ γ₂

variable (X : ChamberSystem ι C) in
@[expose] def PanelShortening (x : C) (γ γ' : List (ι × C)) : Prop :=
  ∃ (γ₁ γ₂ : List (ι × C)) (i : ι) (y z : C), γ = γ₁ ++ [(i, y), (i, z)] ++ γ₂ ∧
    X.adj i (galleryEnd x γ₁) y ∧ X.adj i y z ∧
    ((z ≠ galleryEnd x γ₁ ∧ γ' = γ₁ ++ [(i, z)] ++ γ₂) ∨ (z = galleryEnd x γ₁ ∧ γ' = γ₁ ++ γ₂))

variable (X : ChamberSystem ι C) (cs) in
@[expose] def ReductionStep (x : C) (γ γ' : List (ι × C)) : Prop :=
  X.StrictMove cs x γ γ' ∨ X.PanelShortening x γ γ'

theorem encard_singleton_le_two' (i : ι) : ({i} : Set ι).encard ≤ 2 := by
  rw [Set.encard_singleton]
  norm_num

namespace ConstantDeletion

variable {x : C} {γ γ' : List (ι × C)}

theorem elemMove (h : ConstantDeletion x γ γ') : X.ElemMove x γ γ' := by
  obtain ⟨γ₁, γ₂, i, rfl, rfl⟩ := h
  simpa using ElemMove.mk (X := X) (x := x) γ₁ [(i, galleryEnd x γ₁)] [] γ₂ {i}
    (encard_singleton_le_two' i) (by simpa using X.adj_refl i _) trivial (by simp) (by simp)
    (by simp)

theorem append_left (α : List (ι × C)) (h : ConstantDeletion (galleryEnd x α) γ γ') :
    ConstantDeletion x (α ++ γ) (α ++ γ') := by
  obtain ⟨γ₁, γ₂, i, rfl, rfl⟩ := h
  exact ⟨α ++ γ₁, γ₂, i, by simp [galleryEnd_append], by simp⟩

end ConstantDeletion

namespace PanelShortening

variable {x : C} {γ γ' : List (ι × C)}

theorem elemMove (h : X.PanelShortening x γ γ') : X.ElemMove x γ γ' := by
  obtain ⟨γ₁, γ₂, i, y, z, rfl, hy, hz, ⟨-, rfl⟩ | ⟨hz', rfl⟩⟩ := h
  · exact .mk γ₁ _ _ γ₂ {i} (encard_singleton_le_two' i) (by simpa using ⟨hy, hz⟩)
      (by simpa using adj_trans hy hz) (by simp) (by simp) (by simp)
  · simpa using ElemMove.mk (X := X) (x := x) γ₁ [(i, y), (i, z)] [] γ₂ {i}
      (encard_singleton_le_two' i) (by simpa using ⟨hy, hz⟩) trivial (by simp) (by simp)
      (by simpa using hz')

theorem galleryEnd_eq (h : X.PanelShortening x γ γ') : galleryEnd x γ = galleryEnd x γ' :=
  h.elemMove.galleryEnd_eq

theorem length_lt (h : X.PanelShortening x γ γ') : γ'.length < γ.length := by
  obtain ⟨γ₁, γ₂, i, y, z, rfl, -, -, ⟨-, rfl⟩ | ⟨-, rfl⟩⟩ := h <;> simp

theorem append_right (h : X.PanelShortening x γ γ') (δ : List (ι × C)) :
    X.PanelShortening x (γ ++ δ) (γ' ++ δ) := by
  obtain ⟨γ₁, γ₂, i, y, z, rfl, hy, hz, ⟨hz', rfl⟩ | ⟨hz', rfl⟩⟩ := h
  · exact ⟨γ₁, γ₂ ++ δ, i, y, z, by simp, hy, hz, Or.inl ⟨hz', by simp⟩⟩
  · exact ⟨γ₁, γ₂ ++ δ, i, y, z, by simp, hy, hz, Or.inr ⟨hz', by simp⟩⟩

end PanelShortening

namespace ReductionStep

variable {x : C} {γ γ' : List (ι × C)}

theorem elemMove (h : X.ReductionStep cs x γ γ') : X.ElemMove x γ γ' :=
  h.elim StrictMove.elemMove PanelShortening.elemMove

theorem append_right (h : X.ReductionStep cs x γ γ') (δ : List (ι × C)) :
    X.ReductionStep cs x (γ ++ δ) (γ' ++ δ) :=
  h.imp (fun h => h.append_right δ) fun h => h.append_right δ

theorem length_le (h : X.ReductionStep cs x γ γ') : γ'.length ≤ γ.length :=
  h.elim (fun h => h.length_eq.le) fun h => h.length_lt.le

end ReductionStep

theorem reflTransGen_reductionStep_twoHomotopic {x : C} {γ γ' : List (ι × C)}
    (h : Relation.ReflTransGen (X.ReductionStep cs x) γ γ') : X.TwoHomotopic x γ γ' :=
  TwoHomotopic.iff_reflTransGen.mpr
    (Relation.ReflTransGen.mono (fun _ _ h => ReductionStep.elemMove h) _ _ h)

theorem reflTransGen_reductionStep_length_le {x : C} {γ γ' : List (ι × C)}
    (h : Relation.ReflTransGen (X.ReductionStep cs x) γ γ') : γ'.length ≤ γ.length := by
  induction h with
  | refl => exact le_rfl
  | tail _ h ih => exact h.length_le.trans ih

theorem exists_isOrdinary_of_isGallery {x : C} {γ : List (ι × C)} (hγ : X.IsGallery x γ) :
    ∃ γ', X.IsOrdinary x γ' ∧ γ'.Sublist γ ∧
      Relation.ReflTransGen (ConstantDeletion x) γ γ' := by
  induction γ generalizing x with
  | nil => exact ⟨[], trivial, .slnil, .refl⟩
  | cons p γ ih =>
    obtain ⟨h1, h2⟩ := hγ
    obtain ⟨γ', h3, h4, h5⟩ := ih h2
    by_cases hp : x = p.2
    · subst hp
      refine ⟨γ', h3, h4.cons p, Relation.ReflTransGen.head ?_ h5⟩
      exact ⟨[], γ, p.1, by simp, by simp⟩
    · refine ⟨p :: γ', ⟨h1, hp, h3⟩, h4.cons_cons p, ?_⟩
      have := h5.lift (fun γ => [p] ++ γ) fun a b h => h.append_left (x := x) [p]
      simpa using this

theorem exists_reduction (hres : ∀ s t : ι, s ≠ t → ∀ y : C, X.IsResidueBuilding cs {s, t} y)
    {x : C} {γ : List (ι × C)} (hγ : X.IsOrdinary x γ) :
    ∃ γ', X.IsReducedOrdinary cs x γ' ∧ Relation.ReflTransGen (X.ReductionStep cs x) γ γ' := by
  obtain ⟨n, hn⟩ : ∃ n, γ.length = n := ⟨_, rfl⟩
  induction n using Nat.strong_induction_on generalizing γ with
  | _ n ih =>
  rcases List.eq_nil_or_concat' γ with rfl | ⟨γ₀, ⟨i, y⟩, rfl⟩
  · exact ⟨[], IsReducedOrdinary.nil x, .refl⟩
  obtain ⟨hγ₀, hp1, hp2⟩ := (isOrdinary_concat x γ₀ (i, y)).mp hγ
  dsimp only at hp1 hp2
  have hlen₀ : γ₀.length < n := by rw [← hn]; simp
  obtain ⟨γ₁, ⟨hγ₁, hred₁⟩, hr₁⟩ := ih _ hlen₀ hγ₀ rfl
  have hend₁ : galleryEnd x γ₁ = galleryEnd x γ₀ :=
    ((reflTransGen_reductionStep_twoHomotopic hr₁).galleryEnd_eq).symm
  have hl₁ : γ₁.length ≤ γ₀.length := reflTransGen_reductionStep_length_le hr₁
  have hr₁' : Relation.ReflTransGen (X.ReductionStep cs x) (γ₀ ++ [(i, y)]) (γ₁ ++ [(i, y)]) :=
    hr₁.lift (· ++ [(i, y)]) fun _ _ h => h.append_right [(i, y)]
  have hγ₁p : X.IsOrdinary x (γ₁ ++ [(i, y)]) :=
    (isOrdinary_concat x γ₁ (i, y)).mpr ⟨hγ₁, hend₁ ▸ hp1, hend₁ ▸ hp2⟩
  by_cases hred : cs.IsReduced (galleryType (γ₁ ++ [(i, y)]))
  · exact ⟨γ₁ ++ [(i, y)], ⟨hγ₁p, hred⟩, hr₁'⟩
  obtain ⟨w, hw⟩ : ∃ w, cs.wordProd (galleryType γ₁) = w := ⟨_, rfl⟩
  have hlw : cs.length w = γ₁.length := by rw [← hw, hred₁.eq, length_galleryType]
  have hdesc : cs.length (w * cs.simple i) + 1 = cs.length w := by
    rcases cs.length_mul_simple w i with h | h
    · exfalso
      apply hred
      rw [CoxeterSystem.IsReduced, galleryType_append, cs.wordProd_append, hw]
      simp [h, hlw]
    · exact h
  obtain ⟨β, hβ, hβw⟩ := cs.exists_isReduced (w * cs.simple i)
  have hβw' : cs.wordProd (β ++ [i]) = w := by
    rw [cs.wordProd_append, ← hβw, cs.wordProd_singleton, mul_assoc, cs.simple_mul_simple_self,
      mul_one]
  have hβi : cs.IsReduced (β ++ [i]) := by
    rw [CoxeterSystem.IsReduced, hβw', List.length_append, List.length_singleton, ← hβ.eq,
      ← hβw]
    omega
  obtain ⟨q, hq⟩ := exists_isBraidPath_index hred₁ hβi (hw.trans hβw'.symm)
  obtain ⟨γ₂, hl, hγ₂, htype₂, hend₂⟩ := exists_isStrictLift hres hq hγ₁ rfl
  have hr₂ : Relation.ReflTransGen (X.ReductionStep cs x) (γ₁ ++ [(i, y)]) (γ₂ ++ [(i, y)]) := by
    have h := StrictHomotopic.iff_reflTransGen.mp
      (hl.strictHomotopic fun e he => hq.isValid_of_mem he)
    have h' : Relation.ReflTransGen (X.ReductionStep cs x) γ₁ γ₂ :=
      Relation.ReflTransGen.mono (fun _ _ h => Or.inl h) _ _ h
    exact h'.lift (· ++ [(i, y)]) fun _ _ h => h.append_right [(i, y)]
  obtain ⟨γ₃, ⟨j, y₀⟩, rfl⟩ : ∃ γ₃ q₀, γ₂ = γ₃ ++ [q₀] := by
    rcases List.eq_nil_or_concat' γ₂ with h | h
    · subst h
      simp at htype₂
    · exact h
  have hj : j = i := by
    rw [galleryType_append] at htype₂
    simpa using (List.append_inj' htype₂ rfl).2
  subst hj
  have hl₃ : γ₃.length + 1 = γ₁.length := by
    have := congrArg List.length htype₂
    simp only [galleryType_append, List.length_append, length_galleryType,
      List.length_singleton, galleryType_cons, galleryType_nil] at this
    rw [← hlw, ← hdesc, hβw, hβ.eq]
    omega
  obtain ⟨hγ₃, hq1, hq2⟩ := (isOrdinary_concat x γ₃ (j, y₀)).mp hγ₂
  dsimp only at hq1 hq2
  rw [galleryEnd_concat] at hend₂
  dsimp only at hend₂
  have hadj2 : X.adj j y₀ y := by rw [hend₂, hend₁]; exact hp1
  have hsplit : γ₃ ++ [(j, y₀)] ++ [(j, y)] = γ₃ ++ [(j, y₀), (j, y)] ++ [] := by simp
  obtain ⟨γ₄, hpanel, hγ₄o, hl₄'⟩ : ∃ γ₄, X.PanelShortening x (γ₃ ++ [(j, y₀)] ++ [(j, y)]) γ₄ ∧
      X.IsOrdinary x γ₄ ∧ γ₄.length ≤ γ₃.length + 1 := by
    by_cases h : y = galleryEnd x γ₃
    · exact ⟨γ₃, ⟨γ₃, [], j, y₀, y, hsplit, hq1, hadj2, Or.inr ⟨h, by simp⟩⟩, hγ₃, by omega⟩
    · exact ⟨γ₃ ++ [(j, y)], ⟨γ₃, [], j, y₀, y, hsplit, hq1, hadj2, Or.inl ⟨h, by simp⟩⟩,
        (isOrdinary_concat x γ₃ (j, y)).mpr ⟨hγ₃, adj_trans hq1 hadj2, Ne.symm h⟩, by simp⟩
  have hl₄ : γ₄.length < n := by
    rw [← hn, List.length_append, List.length_singleton]
    omega
  obtain ⟨γ₅, hγ₅, hr₅⟩ := ih _ hl₄ hγ₄o rfl
  exact ⟨γ₅, hγ₅, hr₁'.trans (hr₂.trans (Relation.ReflTransGen.head (Or.inr hpanel) hr₅))⟩

end ChamberSystem

end CFSG.Monster.B.Geometry
