module

public import CFSG.Monster.B.Geometry.ChamberSystem

public section

namespace CFSG.Monster.B.Geometry

namespace ChamberSystem

universe u v w

variable {I : Type u} {C : Type v} (X : ChamberSystem I C) (c₀ : C)

@[expose] def coverSetoid : Setoid {γ : List (I × C) // X.IsGallery c₀ γ} where
  r a b := X.TwoHomotopic c₀ a.1 b.1
  iseqv := ⟨fun a => .refl a.1, fun h => h.symm, fun h h' => h.trans h'⟩

abbrev Cover : Type (max u v) := Quotient (X.coverSetoid c₀)

open _root_.Classical in
@[expose] noncomputable def cls (γ : List (I × C)) : X.Cover c₀ :=
  if h : X.IsGallery c₀ γ then Quotient.mk (X.coverSetoid c₀) ⟨γ, h⟩
  else Quotient.mk (X.coverSetoid c₀) ⟨[], trivial⟩

@[expose] noncomputable def coverBase : X.Cover c₀ := X.cls c₀ []

@[expose] def coverProj : X.Cover c₀ → C :=
  Quotient.lift (fun a => galleryEnd c₀ a.1) fun _ _ h => TwoHomotopic.galleryEnd_eq h

@[expose] def coverAdj (i : I) (a b : X.Cover c₀) : Prop :=
  ∃ γ : List (I × C), ∃ y : C, X.IsGallery c₀ γ ∧ X.adj i (galleryEnd c₀ γ) y ∧
    ((a = X.cls c₀ γ ∧ b = X.cls c₀ (γ ++ [(i, y)])) ∨
      (b = X.cls c₀ γ ∧ a = X.cls c₀ (γ ++ [(i, y)])))

variable {X c₀}

theorem cls_of_isGallery {γ : List (I × C)} (hγ : X.IsGallery c₀ γ) :
    X.cls c₀ γ = Quotient.mk (X.coverSetoid c₀) ⟨γ, hγ⟩ := by
  rw [cls, dite_eq_left hγ]

theorem cls_eq_iff {γ γ' : List (I × C)} (hγ : X.IsGallery c₀ γ) (hγ' : X.IsGallery c₀ γ') :
    X.cls c₀ γ = X.cls c₀ γ' ↔ X.TwoHomotopic c₀ γ γ' := by
  rw [cls_of_isGallery hγ, cls_of_isGallery hγ', Quotient.eq]
  rfl

theorem cls_congr {γ γ' : List (I × C)} (h : X.TwoHomotopic c₀ γ γ') :
    X.cls c₀ γ = X.cls c₀ γ' := by
  by_cases hγ : X.IsGallery c₀ γ
  · exact (cls_eq_iff hγ (h.isGallery_iff.mp hγ)).mpr h
  · have hγ' : ¬X.IsGallery c₀ γ' := fun h' => hγ (h.isGallery_iff.mpr h')
    rw [cls, dite_eq_right hγ, cls, dite_eq_right hγ']

theorem exists_eq_cls (a : X.Cover c₀) : ∃ γ, X.IsGallery c₀ γ ∧ a = X.cls c₀ γ := by
  induction a using Quotient.inductionOn with
  | h a => exact ⟨a.1, a.2, (cls_of_isGallery a.2).symm⟩

@[simp] theorem coverProj_cls {γ : List (I × C)} (hγ : X.IsGallery c₀ γ) :
    X.coverProj c₀ (X.cls c₀ γ) = galleryEnd c₀ γ := by
  rw [cls_of_isGallery hγ]
  rfl

@[simp] theorem coverProj_coverBase : X.coverProj c₀ (X.coverBase c₀) = c₀ :=
  coverProj_cls (γ := []) trivial

theorem coverAdj_cls_iff {γ : List (I × C)} (hγ : X.IsGallery c₀ γ) {i : I}
    {b : X.Cover c₀} :
    X.coverAdj c₀ i (X.cls c₀ γ) b ↔
      ∃ y, X.adj i (galleryEnd c₀ γ) y ∧ b = X.cls c₀ (γ ++ [(i, y)]) := by
  constructor
  · rintro ⟨δ, y, hδ, hy, ⟨h1, rfl⟩ | ⟨rfl, h2⟩⟩
    · have hγδ := (cls_eq_iff hγ hδ).mp h1
      refine ⟨y, hγδ.galleryEnd_eq ▸ hy, cls_congr (hγδ.append_right _).symm⟩
    · have hδy : X.IsGallery c₀ (δ ++ [(i, y)]) := (isGallery_concat _ _ _).mpr ⟨hδ, hy⟩
      have hγδ := (cls_eq_iff hγ hδy).mp h2
      have hend : galleryEnd c₀ γ = y := by rw [hγδ.galleryEnd_eq, galleryEnd_concat]
      refine ⟨galleryEnd c₀ δ, hend ▸ adj_symm hy, ?_⟩
      have h3 := twoHomotopic_backtrack (X := X) (x := c₀) δ [] hy
      simp only [List.append_nil] at h3
      rw [cls_congr (hγδ.append_right [(i, galleryEnd c₀ δ)]), ← cls_congr h3]
      simp
  · rintro ⟨y, hy, rfl⟩
    exact ⟨γ, y, hγ, hy, Or.inl ⟨rfl, rfl⟩⟩

theorem coverAdj_refl (i : I) (a : X.Cover c₀) : X.coverAdj c₀ i a a := by
  obtain ⟨γ, hγ, rfl⟩ := exists_eq_cls a
  refine (coverAdj_cls_iff hγ).mpr ⟨galleryEnd c₀ γ, X.adj_refl i _, ?_⟩
  have h := twoHomotopic_constant (X := X) (x := c₀) γ [] i
  rw [List.append_nil, List.append_nil] at h
  exact (cls_congr h).symm

theorem coverAdj_symm {i : I} {a b : X.Cover c₀} (h : X.coverAdj c₀ i a b) :
    X.coverAdj c₀ i b a := by
  obtain ⟨γ, y, hγ, hy, h⟩ := h
  exact ⟨γ, y, hγ, hy, h.symm⟩

theorem coverAdj_trans {i : I} {a b c : X.Cover c₀} (hab : X.coverAdj c₀ i a b)
    (hbc : X.coverAdj c₀ i b c) : X.coverAdj c₀ i a c := by
  obtain ⟨γ, hγ, rfl⟩ := exists_eq_cls a
  obtain ⟨y, hy, rfl⟩ := (coverAdj_cls_iff hγ).mp hab
  have hγy : X.IsGallery c₀ (γ ++ [(i, y)]) := (isGallery_concat _ _ _).mpr ⟨hγ, hy⟩
  obtain ⟨z, hz, rfl⟩ := (coverAdj_cls_iff hγy).mp hbc
  rw [galleryEnd_concat] at hz
  refine (coverAdj_cls_iff hγ).mpr ⟨z, adj_trans hy hz, ?_⟩
  have h := twoHomotopic_panel (X := X) (x := c₀) γ [] hy hz
  simp only [List.append_nil] at h
  rw [← cls_congr h]
  simp

variable (X c₀) in
@[expose] noncomputable def universalCover : ChamberSystem I (X.Cover c₀) where
  adj := X.coverAdj c₀
  equivalence _ := ⟨coverAdj_refl _, coverAdj_symm, coverAdj_trans⟩

theorem universalCover_adj_cls_iff {γ : List (I × C)} (hγ : X.IsGallery c₀ γ) {i : I}
    {b : X.Cover c₀} :
    (X.universalCover c₀).adj i (X.cls c₀ γ) b ↔
      ∃ y, X.adj i (galleryEnd c₀ γ) y ∧ b = X.cls c₀ (γ ++ [(i, y)]) :=
  coverAdj_cls_iff hγ

theorem isMorphism_coverProj : IsMorphism (X.universalCover c₀) X (X.coverProj c₀) := by
  intro i a b h
  obtain ⟨γ, hγ, rfl⟩ := exists_eq_cls a
  obtain ⟨y, hy, rfl⟩ := (universalCover_adj_cls_iff hγ).mp h
  rw [coverProj_cls hγ, coverProj_cls ((isGallery_concat _ _ _).mpr ⟨hγ, hy⟩),
    galleryEnd_concat]
  exact hy

theorem coverProj_surjective (hX : X.Connected) : Function.Surjective (X.coverProj c₀) := by
  intro c
  obtain ⟨γ, hγ, rfl⟩ := hX c₀ c
  exact ⟨X.cls c₀ γ, coverProj_cls hγ⟩

variable (X c₀) in
@[expose] noncomputable def liftCls : List (I × C) → List (I × C) → List (I × X.Cover c₀)
  | _, [] => []
  | α, p :: η => (p.1, X.cls c₀ (α ++ [p])) :: liftCls (α ++ [p]) η

@[simp] theorem liftCls_nil (α : List (I × C)) : X.liftCls c₀ α [] = [] := rfl

@[simp] theorem liftCls_cons (α : List (I × C)) (p : I × C) (η : List (I × C)) :
    X.liftCls c₀ α (p :: η) = (p.1, X.cls c₀ (α ++ [p])) :: X.liftCls c₀ (α ++ [p]) η :=
  rfl

theorem liftCls_append (α η η' : List (I × C)) :
    X.liftCls c₀ α (η ++ η') = X.liftCls c₀ α η ++ X.liftCls c₀ (α ++ η) η' := by
  induction η generalizing α with
  | nil => simp
  | cons p η ih => simp [ih]

@[simp] theorem galleryType_liftCls (α η : List (I × C)) :
    galleryType (X.liftCls c₀ α η) = galleryType η := by
  induction η generalizing α with
  | nil => rfl
  | cons p η ih => simp [ih]

@[simp] theorem galleryEnd_liftCls (α η : List (I × C)) :
    galleryEnd (X.cls c₀ α) (X.liftCls c₀ α η) = X.cls c₀ (α ++ η) := by
  induction η generalizing α with
  | nil => simp
  | cons p η ih => simp [ih]

theorem isGallery_liftCls {α η : List (I × C)} (hα : X.IsGallery c₀ α)
    (hη : X.IsGallery (galleryEnd c₀ α) η) :
    (X.universalCover c₀).IsGallery (X.cls c₀ α) (X.liftCls c₀ α η) := by
  induction η generalizing α with
  | nil => trivial
  | cons p η ih =>
    obtain ⟨h1, h2⟩ := hη
    have hαp : X.IsGallery c₀ (α ++ [p]) := (isGallery_concat _ _ _).mpr ⟨hα, h1⟩
    refine ⟨(universalCover_adj_cls_iff hα).mpr ⟨p.2, h1, rfl⟩, ih hαp ?_⟩
    rwa [galleryEnd_concat]

theorem galleryMap_coverProj_liftCls {α η : List (I × C)} (hα : X.IsGallery c₀ α)
    (hη : X.IsGallery (galleryEnd c₀ α) η) :
    galleryMap (X.coverProj c₀) (X.liftCls c₀ α η) = η := by
  induction η generalizing α with
  | nil => rfl
  | cons p η ih =>
    obtain ⟨h1, h2⟩ := hη
    have hαp : X.IsGallery c₀ (α ++ [p]) := (isGallery_concat _ _ _).mpr ⟨hα, h1⟩
    rw [liftCls_cons, galleryMap_cons, coverProj_cls hαp, galleryEnd_concat,
      ih hαp (by rwa [galleryEnd_concat])]

theorem liftCls_congr {α α' : List (I × C)} (h : X.TwoHomotopic c₀ α α') (η : List (I × C)) :
    X.liftCls c₀ α η = X.liftCls c₀ α' η := by
  induction η generalizing α α' with
  | nil => rfl
  | cons p η ih =>
    rw [liftCls_cons, liftCls_cons, cls_congr (h.append_right [p]), ih (h.append_right [p])]

theorem eq_liftCls {α : List (I × C)} (hα : X.IsGallery c₀ α) {Γ : List (I × X.Cover c₀)}
    (hΓ : (X.universalCover c₀).IsGallery (X.cls c₀ α) Γ) :
    Γ = X.liftCls c₀ α (galleryMap (X.coverProj c₀) Γ) := by
  induction Γ generalizing α with
  | nil => rfl
  | cons p Γ ih =>
    obtain ⟨i, b⟩ := p
    obtain ⟨h1, h2⟩ := hΓ
    dsimp only at h1 h2
    obtain ⟨y, hy, rfl⟩ := (universalCover_adj_cls_iff hα).mp h1
    have hαy : X.IsGallery c₀ (α ++ [(i, y)]) := (isGallery_concat _ _ _).mpr ⟨hα, hy⟩
    simp only [galleryMap_cons, liftCls_cons, coverProj_cls hαy, galleryEnd_concat]
    rw [← ih hαy h2]

theorem TwoHomotopic.liftCls {α η η' : List (I × C)} (hα : X.IsGallery c₀ α)
    (h : X.TwoHomotopic (galleryEnd c₀ α) η η') (hη : X.IsGallery (galleryEnd c₀ α) η) :
    (X.universalCover c₀).TwoHomotopic (X.cls c₀ α) (X.liftCls c₀ α η) (X.liftCls c₀ α η') := by
  rw [TwoHomotopic.iff_reflTransGen] at h
  induction h with
  | refl => rfl
  | @tail η₁ η₂ h12 hm ih =>
    refine ih.trans ?_
    have hη₁ : X.IsGallery (galleryEnd c₀ α) η₁ :=
      (TwoHomotopic.iff_reflTransGen.mpr h12).isGallery_iff.mp hη
    clear ih h12
    obtain ⟨β, ζ, ζ', δ, J, hJ, hζ, hζ', hζJ, hζ'J, hend⟩ := hm
    have hβ : X.IsGallery (galleryEnd c₀ α) β := (List.append_assoc β ζ δ ▸ hη₁).of_append_left
    have hαβ : X.IsGallery c₀ (α ++ β) := hα.append hβ
    rw [← galleryEnd_append c₀ α β] at hζ hζ' hend
    have hmove : X.ElemMove c₀ (α ++ β ++ ζ ++ []) (α ++ β ++ ζ' ++ []) :=
      .mk (α ++ β) ζ ζ' [] J hJ hζ hζ' hζJ hζ'J hend
    simp only [List.append_nil] at hmove
    have hcl : X.liftCls c₀ (α ++ (β ++ ζ)) δ = X.liftCls c₀ (α ++ (β ++ ζ')) δ := by
      rw [← List.append_assoc, ← List.append_assoc]
      exact liftCls_congr (.of_elemMove hmove) δ
    rw [liftCls_append, liftCls_append, liftCls_append, liftCls_append, hcl]
    refine .of_elemMove (.mk _ _ _ _ J hJ ?_ ?_ (by simpa using hζJ) (by simpa using hζ'J) ?_)
    · rw [galleryEnd_liftCls]; exact isGallery_liftCls hαβ hζ
    · rw [galleryEnd_liftCls]; exact isGallery_liftCls hαβ hζ'
    · rw [galleryEnd_liftCls, galleryEnd_liftCls, galleryEnd_liftCls,
        cls_congr (.of_elemMove hmove)]

theorem universalCover_connected : (X.universalCover c₀).Connected := by
  intro a b
  obtain ⟨α, hα, rfl⟩ := exists_eq_cls a
  obtain ⟨β, hβ, rfl⟩ := exists_eq_cls b
  have hLα := isGallery_liftCls (c₀ := c₀) (α := []) trivial hα
  have hLβ := isGallery_liftCls (c₀ := c₀) (α := []) trivial hβ
  have hLend : galleryEnd (X.cls c₀ []) (X.liftCls c₀ [] α) = X.cls c₀ α := by
    rw [galleryEnd_liftCls, List.nil_append]
  have hrev : galleryEnd (X.cls c₀ α) (galleryReverse (X.cls c₀ []) (X.liftCls c₀ [] α)) =
      X.cls c₀ [] := by
    rw [← hLend, galleryEnd_galleryReverse]
  refine ⟨galleryReverse (X.cls c₀ []) (X.liftCls c₀ [] α) ++ X.liftCls c₀ [] β, ?_, ?_⟩
  · have h1 := hLα.reverse
    rw [hLend] at h1
    refine h1.append ?_
    rw [hrev]
    exact hLβ
  · rw [galleryEnd_append, hrev, galleryEnd_liftCls, List.nil_append]

theorem mem_residue_universalCover_iff {γ : List (I × C)} (hγ : X.IsGallery c₀ γ) {J : Set I}
    {b : X.Cover c₀} :
    b ∈ (X.universalCover c₀).residue J (X.cls c₀ γ) ↔
      ∃ η, X.IsGallery (galleryEnd c₀ γ) η ∧ (∀ i ∈ galleryType η, i ∈ J) ∧
        b = X.cls c₀ (γ ++ η) := by
  constructor
  · rintro ⟨Γ, hΓ, hJ, rfl⟩
    have hΓη := isMorphism_coverProj.isGallery hΓ
    rw [coverProj_cls hγ] at hΓη
    refine ⟨_, hΓη, by simpa using hJ, ?_⟩
    conv_lhs => rw [eq_liftCls hγ hΓ]
    rw [galleryEnd_liftCls]
  · rintro ⟨η, hη, hJ, rfl⟩
    exact ⟨_, isGallery_liftCls hγ hη, by simpa using hJ, galleryEnd_liftCls _ _⟩

theorem isResidueIso_coverProj {J : Set I} (hJ : J.encard ≤ 2) (a : X.Cover c₀) :
    IsResidueIso (X.universalCover c₀) X (X.coverProj c₀) J a := by
  obtain ⟨γ, hγ, rfl⟩ := exists_eq_cls a
  have hinj : Set.InjOn (X.coverProj c₀) ((X.universalCover c₀).residue J (X.cls c₀ γ)) := by
    intro b hb b' hb' hbb'
    obtain ⟨η, hη, hηJ, rfl⟩ := (mem_residue_universalCover_iff hγ).mp hb
    obtain ⟨η', hη', hη'J, rfl⟩ := (mem_residue_universalCover_iff hγ).mp hb'
    rw [coverProj_cls (hγ.append hη), coverProj_cls (hγ.append hη'), galleryEnd_append,
      galleryEnd_append] at hbb'
    have h := twoHomotopic_replace (X := X) (x := c₀) γ η η' [] hJ hη hη' hηJ hη'J hbb'
    simp only [List.append_nil] at h
    exact cls_congr h
  refine ⟨⟨isMorphism_coverProj.mapsTo_residue J _, hinj, ?_⟩, ?_⟩
  · rintro d ⟨η, hη, hηJ, rfl⟩
    rw [coverProj_cls hγ] at hη ⊢
    refine ⟨X.cls c₀ (γ ++ η), (mem_residue_universalCover_iff hγ).mpr ⟨η, hη, hηJ, rfl⟩, ?_⟩
    rw [coverProj_cls (hγ.append hη), galleryEnd_append]
  · intro b hb b' hb' j hj
    refine ⟨fun h => ?_, isMorphism_coverProj j b b'⟩
    obtain ⟨η, hη, hηJ, rfl⟩ := (mem_residue_universalCover_iff hγ).mp hb
    have hγη := hγ.append hη
    rw [coverProj_cls hγη] at h
    set y := X.coverProj c₀ b' with hy
    have hγηy : X.IsGallery c₀ (γ ++ η ++ [(j, y)]) := (isGallery_concat _ _ _).mpr ⟨hγη, h⟩
    have hmem : X.cls c₀ (γ ++ η ++ [(j, y)]) ∈
        (X.universalCover c₀).residue J (X.cls c₀ γ) := by
      refine (mem_residue_universalCover_iff hγ).mpr ⟨η ++ [(j, y)], ?_, ?_, by simp⟩
      · exact (isGallery_concat _ _ _).mpr ⟨hη, by rwa [← galleryEnd_append]⟩
      · intro i hi
        simp only [galleryType_append, List.mem_append, galleryType_cons, galleryType_nil,
          List.mem_singleton] at hi
        rcases hi with hi | rfl
        · exact hηJ i hi
        · exact hj
    have heq : X.cls c₀ (γ ++ η ++ [(j, y)]) = b' :=
      hinj hmem hb' (by rw [coverProj_cls hγηy, galleryEnd_concat])
    rw [← heq]
    exact (universalCover_adj_cls_iff hγη).mpr ⟨y, h, rfl⟩

theorem bijOn_coverProj_panel (i : I) (a : X.Cover c₀) :
    Set.BijOn (X.coverProj c₀) ((X.universalCover c₀).residue {i} a)
      (X.residue {i} (X.coverProj c₀ a)) :=
  (isResidueIso_coverProj (encard_singleton_le_two i) a).1

theorem simplyTwoConnected_universalCover : (X.universalCover c₀).SimplyTwoConnected := by
  intro a Γ hΓ hclosed
  obtain ⟨γ, hγ, rfl⟩ := exists_eq_cls a
  set η := galleryMap (X.coverProj c₀) Γ with hη_def
  have hΓeq : Γ = X.liftCls c₀ γ η := eq_liftCls hγ hΓ
  have hη : X.IsGallery (galleryEnd c₀ γ) η := by
    have := isMorphism_coverProj.isGallery hΓ
    rwa [coverProj_cls hγ] at this
  have hγη : X.IsGallery c₀ (γ ++ η) := hγ.append hη
  have hloop : X.TwoHomotopic c₀ (γ ++ η) γ := by
    refine (cls_eq_iff hγη hγ).mp ?_
    rw [← galleryEnd_liftCls, ← hΓeq, hclosed]
  set L := X.liftCls c₀ [] γ with hL
  have hLg : (X.universalCover c₀).IsGallery (X.cls c₀ []) L :=
    isGallery_liftCls (α := []) trivial hγ
  have hLend : galleryEnd (X.cls c₀ []) L = X.cls c₀ γ := by
    rw [hL, galleryEnd_liftCls, List.nil_append]
  have h1 : (X.universalCover c₀).TwoHomotopic (X.cls c₀ []) (L ++ Γ) L := by
    have := TwoHomotopic.liftCls (α := []) trivial hloop hγη
    rwa [liftCls_append, List.nil_append, ← hΓeq] at this
  have h2 := twoHomotopic_reverse_append hLg
  rw [hLend] at h2
  have h3 : (X.universalCover c₀).TwoHomotopic (X.cls c₀ γ)
      (galleryReverse (X.cls c₀ []) L ++ (L ++ Γ)) (galleryReverse (X.cls c₀ []) L ++ L) := by
    refine TwoHomotopic.append_left _ ?_
    rw [← hLend, galleryEnd_galleryReverse]
    exact h1
  have h4 : (X.universalCover c₀).TwoHomotopic (X.cls c₀ γ) Γ
      (galleryReverse (X.cls c₀ []) L ++ (L ++ Γ)) := by
    have := (h2.append_right Γ).symm
    rwa [List.nil_append, List.append_assoc] at this
  exact (h4.trans h3).trans h2

section Universal

variable {E : Type w} {Y : ChamberSystem I E}

variable (X c₀) in
@[expose] noncomputable def coverLift (Y : ChamberSystem I E) (q : E → C) (d₀ : E) :
    X.Cover c₀ → E :=
  fun a => galleryEnd d₀ (liftGallery Y q d₀ (Quotient.out a).1)

variable {q : E → C} {d₀ : E} (hq : ∀ J : Set I, J.encard ≤ 2 → ∀ e, IsResidueIso Y X q J e)
  (hd₀ : q d₀ = c₀)
include hq hd₀

omit hd₀ in
theorem bijOn_panel_of_isResidueIso (i : I) (e : E) :
    Set.BijOn q (Y.residue {i} e) (X.residue {i} (q e)) :=
  (hq {i} (encard_singleton_le_two i) e).1

theorem coverLift_cls {γ : List (I × C)} (hγ : X.IsGallery c₀ γ) :
    X.coverLift c₀ Y q d₀ (X.cls c₀ γ) = galleryEnd d₀ (liftGallery Y q d₀ γ) := by
  have hout : X.TwoHomotopic c₀ (Quotient.out (X.cls c₀ γ)).1 γ := by
    rw [cls_of_isGallery hγ]
    exact Quotient.mk_out (s := X.coverSetoid c₀) ⟨γ, hγ⟩
  have hgal : X.IsGallery c₀ (Quotient.out (X.cls c₀ γ)).1 := (Quotient.out (X.cls c₀ γ)).2
  subst hd₀
  exact galleryEnd_liftGallery_eq (bijOn_panel_of_isResidueIso hq)
    (fun J hJ e => (hq J hJ e).injOn) hout hgal

theorem coverLift_coverBase : X.coverLift c₀ Y q d₀ (X.coverBase c₀) = d₀ :=
  coverLift_cls hq hd₀ (γ := []) trivial

theorem coverLift_spec (a : X.Cover c₀) : q (X.coverLift c₀ Y q d₀ a) = X.coverProj c₀ a := by
  obtain ⟨γ, hγ, rfl⟩ := exists_eq_cls a
  rw [coverLift_cls hq hd₀ hγ, coverProj_cls hγ]
  have hγ' : X.IsGallery (q d₀) γ := hd₀ ▸ hγ
  rw [galleryEnd_liftGallery (bijOn_panel_of_isResidueIso hq) hγ', hd₀]

theorem isMorphism_coverLift : IsMorphism (X.universalCover c₀) Y (X.coverLift c₀ Y q d₀) := by
  intro i a b h
  obtain ⟨γ, hγ, rfl⟩ := exists_eq_cls a
  obtain ⟨y, hy, rfl⟩ := (universalCover_adj_cls_iff hγ).mp h
  have hγy : X.IsGallery c₀ (γ ++ [(i, y)]) := (isGallery_concat _ _ _).mpr ⟨hγ, hy⟩
  rw [coverLift_cls hq hd₀ hγ, coverLift_cls hq hd₀ hγy, liftGallery_append, galleryEnd_append]
  simp only [liftGallery_cons, liftGallery_nil, galleryEnd_cons, galleryEnd_nil]
  refine (liftStep_spec (bijOn_panel_of_isResidueIso hq) ?_).1
  have hγ' : X.IsGallery (q d₀) γ := hd₀ ▸ hγ
  rw [galleryEnd_liftGallery (bijOn_panel_of_isResidueIso hq) hγ', hd₀]
  exact hy

theorem eq_coverLift {g : X.Cover c₀ → E} (hg : IsMorphism (X.universalCover c₀) Y g)
    (hg₀ : g (X.coverBase c₀) = d₀) (hgq : ∀ a, q (g a) = X.coverProj c₀ a) :
    g = X.coverLift c₀ Y q d₀ :=
  eq_of_comp_eq universalCover_connected (fun i e => (bijOn_panel_of_isResidueIso hq i e).injOn)
    hg (isMorphism_coverLift hq hd₀) (fun a => by rw [hgq, coverLift_spec hq hd₀])
    (hg₀.trans (coverLift_coverBase hq hd₀).symm)

theorem coverLift_surjective (hY : Y.Connected) (hqm : IsMorphism Y X q) :
    Function.Surjective (X.coverLift c₀ Y q d₀) := by
  intro e
  obtain ⟨Δ, hΔ, rfl⟩ := hY d₀ e
  have hγ : X.IsGallery c₀ (galleryMap q Δ) := hd₀ ▸ hqm.isGallery hΔ
  refine ⟨X.cls c₀ (galleryMap q Δ), ?_⟩
  rw [coverLift_cls hq hd₀ hγ, liftGallery_galleryMap (bijOn_panel_of_isResidueIso hq) hΔ]

theorem isResidueIso_coverLift (hqm : IsMorphism Y X q) {J : Set I} (hJ : J.encard ≤ 2)
    (a : X.Cover c₀) : IsResidueIso (X.universalCover c₀) Y (X.coverLift c₀ Y q d₀) J a := by
  set f := X.coverLift c₀ Y q d₀ with hf
  have hfm : IsMorphism (X.universalCover c₀) Y f := isMorphism_coverLift hq hd₀
  have hπ := isResidueIso_coverProj (X := X) (c₀ := c₀) hJ a
  have hqJ := hq J hJ (f a)
  have hfa : q (f a) = X.coverProj c₀ a := coverLift_spec hq hd₀ a
  refine ⟨⟨hfm.mapsTo_residue J a, fun b hb b' hb' hbb' => hπ.injOn hb hb' ?_, ?_⟩, ?_⟩
  · rw [← coverLift_spec hq hd₀ b, ← coverLift_spec hq hd₀ b', ← hf, hbb']
  · intro e he
    have hqe : q e ∈ X.residue J (X.coverProj c₀ a) := hfa ▸ hqm.mapsTo_residue J (f a) he
    obtain ⟨b, hb, hbe⟩ := hπ.1.surjOn hqe
    refine ⟨b, hb, hqJ.injOn (hfm.mapsTo_residue J a hb) he ?_⟩
    rw [hf, coverLift_spec hq hd₀ b, hbe]
  · intro b hb b' hb' j hj
    refine ⟨fun h => ?_, hfm j b b'⟩
    have h' := hqm j _ _ h
    rw [coverLift_spec hq hd₀ b, coverLift_spec hq hd₀ b'] at h'
    exact (hπ.2 b hb b' hb' j hj).mp h'

end Universal

theorem chamber_universal_two_cover (hX : X.Connected) :
    (X.universalCover c₀).Connected ∧
    IsMorphism (X.universalCover c₀) X (X.coverProj c₀) ∧
    Function.Surjective (X.coverProj c₀) ∧
    X.coverProj c₀ (X.coverBase c₀) = c₀ ∧
    (∀ J : Set I, J.encard ≤ 2 → ∀ a,
      IsResidueIso (X.universalCover c₀) X (X.coverProj c₀) J a) ∧
    (∀ {E : Type w} (Y : ChamberSystem I E) (d₀ : E) (q : E → C), Y.Connected →
      IsMorphism Y X q → q d₀ = c₀ → (∀ J : Set I, J.encard ≤ 2 → ∀ e, IsResidueIso Y X q J e) →
      ∃ f : X.Cover c₀ → E,
        (IsMorphism (X.universalCover c₀) Y f ∧ f (X.coverBase c₀) = d₀ ∧
          q ∘ f = X.coverProj c₀) ∧
        Function.Surjective f ∧
        (∀ J : Set I, J.encard ≤ 2 → ∀ a, IsResidueIso (X.universalCover c₀) Y f J a) ∧
        ∀ g : X.Cover c₀ → E, IsMorphism (X.universalCover c₀) Y g →
          g (X.coverBase c₀) = d₀ → q ∘ g = X.coverProj c₀ → g = f) ∧
    (X.universalCover c₀).SimplyTwoConnected ∧
    (∀ a : X.Cover c₀, ∃ γ, X.IsGallery c₀ γ ∧ a = X.cls c₀ γ) ∧
    (∀ γ γ', X.IsGallery c₀ γ → X.IsGallery c₀ γ' →
      (X.cls c₀ γ = X.cls c₀ γ' ↔ X.TwoHomotopic c₀ γ γ')) ∧
    (∀ γ, X.IsGallery c₀ γ → X.coverProj c₀ (X.cls c₀ γ) = galleryEnd c₀ γ) ∧
    (∀ (i : I) (a b : X.Cover c₀), (X.universalCover c₀).adj i a b ↔
      ∃ γ y, X.IsGallery c₀ γ ∧ X.adj i (galleryEnd c₀ γ) y ∧
        ((a = X.cls c₀ γ ∧ b = X.cls c₀ (γ ++ [(i, y)])) ∨
          (b = X.cls c₀ γ ∧ a = X.cls c₀ (γ ++ [(i, y)])))) ∧
    X.coverBase c₀ = X.cls c₀ [] := by
  refine ⟨universalCover_connected, isMorphism_coverProj, coverProj_surjective hX,
    coverProj_coverBase, fun J hJ a => isResidueIso_coverProj hJ a, ?_,
    simplyTwoConnected_universalCover, exists_eq_cls, fun γ γ' hγ hγ' => cls_eq_iff hγ hγ',
    fun γ hγ => coverProj_cls hγ, fun i a b => Iff.rfl, rfl⟩
  intro E Y d₀ q hY hqm hd₀ hq
  refine ⟨X.coverLift c₀ Y q d₀, ⟨isMorphism_coverLift hq hd₀, coverLift_coverBase hq hd₀,
    funext (coverLift_spec hq hd₀)⟩, coverLift_surjective hq hd₀ hY hqm,
    fun J hJ a => isResidueIso_coverLift hq hd₀ hqm hJ a, ?_⟩
  intro g hg hg₀ hgq
  exact eq_coverLift hq hd₀ hg hg₀ fun a => congrFun hgq a

end ChamberSystem

end CFSG.Monster.B.Geometry
