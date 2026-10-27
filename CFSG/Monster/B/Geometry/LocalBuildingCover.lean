module

public import CFSG.Monster.B.Geometry.StrictRigidity
public import CFSG.Monster.B.Geometry.NormalFormCover

public section

namespace CFSG.Monster.B.Geometry

open CoxeterSystem CFSG.LieType.Chevalley.CosetBuilding CFSG.GroupActions.Exchange

namespace ChamberSystem

variable {ι : Type*} {M : CoxeterMatrix ι} {W : Type*} [Group W] {cs : CoxeterSystem M W}
variable {C : Type*} {X : ChamberSystem ι C} {c₀ : C}

theorem cls_out (A : X.Cover c₀) : X.cls c₀ (Quotient.out A).1 = A := by
  rw [cls_of_isGallery (Quotient.out A).2]
  exact Quotient.out_eq A

theorem twoHomotopic_of_append_left {α η η' : List (ι × C)} (hα : X.IsGallery c₀ α)
    (h : X.TwoHomotopic c₀ (α ++ η) (α ++ η')) : X.TwoHomotopic (galleryEnd c₀ α) η η' := by
  have h1 : X.TwoHomotopic (galleryEnd c₀ α) (galleryReverse c₀ α ++ (α ++ η))
      (galleryReverse c₀ α ++ (α ++ η')) :=
    TwoHomotopic.append_left _ (by rw [galleryEnd_galleryReverse]; exact h)
  have h2 : ∀ ζ, X.TwoHomotopic (galleryEnd c₀ α) (galleryReverse c₀ α ++ (α ++ ζ)) ζ := by
    intro ζ
    rw [← List.append_assoc]
    simpa using (twoHomotopic_reverse_append hα).append_right ζ
  exact (h2 η).symm.trans (h1.trans (h2 η'))

theorem twoHomotopic_append_of_reverse {α β η : List (ι × C)} (hα : X.IsGallery c₀ α)
    (h : X.TwoHomotopic (galleryEnd c₀ α) (galleryReverse c₀ α ++ β) η) :
    X.TwoHomotopic c₀ β (α ++ η) := by
  have h1 := TwoHomotopic.append_left (x := c₀) α h
  have h2 : X.TwoHomotopic c₀ β (α ++ (galleryReverse c₀ α ++ β)) := by
    rw [← List.append_assoc]
    simpa using ((twoHomotopic_append_reverse hα).append_right β).symm
  exact h2.trans h1

theorem isReducedOrdinary_singleton {x y : C} {i : ι} (hy : X.adj i x y) (hne : x ≠ y) :
    X.IsReducedOrdinary cs x [(i, y)] :=
  ⟨by simpa using ⟨hy, hne⟩, by simp [CoxeterSystem.IsReduced, cs.length_simple]⟩

variable (X cs) in
open _root_.Classical in
noncomputable def coverDist (c₀ : C) (A B : X.Cover c₀) : W :=
  if h : ∃ ρ, X.IsReducedOrdinary cs (galleryEnd c₀ (Quotient.out A).1) ρ ∧
      X.cls c₀ ((Quotient.out A).1 ++ ρ) = B then cs.wordProd (galleryType h.choose)
  else 1

variable (hres : ∀ s t : ι, s ≠ t → ∀ y : C, X.IsResidueBuilding cs {s, t} y)
include hres

theorem exists_cls_append {α : List (ι × C)} (hα : X.IsGallery c₀ α) (B : X.Cover c₀) :
    ∃ ρ, X.IsReducedOrdinary cs (galleryEnd c₀ α) ρ ∧ B = X.cls c₀ (α ++ ρ) := by
  obtain ⟨β, hβ, rfl⟩ := exists_eq_cls B
  have hη : X.IsGallery (galleryEnd c₀ α) (galleryReverse c₀ α ++ β) :=
    hα.reverse.append (by rw [galleryEnd_galleryReverse]; exact hβ)
  obtain ⟨ρ, hρ, h⟩ := exists_twoHomotopic_isReducedOrdinary hres hη
  exact ⟨ρ, hρ, cls_congr (twoHomotopic_append_of_reverse hα h)⟩

variable [Nontrivial ι] [Finite W] (h3 : ∀ T : Finset ι, T.card ≤ 3 → ∀ y : C,
  ∃ T' : Set ι, (T : Set ι) ⊆ T' ∧ X.IsResidueBuilding cs T' y)
include h3

theorem strictHomotopic_of_twoHomotopic' {y : C} {ρ ρ' : List (ι × C)}
    (hρ : X.IsReducedOrdinary cs y ρ) (hρ' : X.IsReducedOrdinary cs y ρ')
    (h : X.TwoHomotopic y ρ ρ') : X.StrictHomotopic cs y ρ ρ' :=
  strictHomotopic_of_twoHomotopic hres (fun _ _ hγ h ht => eq_of_strictHomotopic hres h3 hγ h ht)
    hρ hρ' h

theorem coverDist_cls_append {α ρ : List (ι × C)} (hα : X.IsGallery c₀ α)
    (hρ : X.IsReducedOrdinary cs (galleryEnd c₀ α) ρ) :
    X.coverDist cs c₀ (X.cls c₀ α) (X.cls c₀ (α ++ ρ)) = cs.wordProd (galleryType ρ) := by
  have hα₀ : X.IsGallery c₀ (Quotient.out (X.cls c₀ α)).1 := (Quotient.out (X.cls c₀ α)).2
  have h₀ : X.TwoHomotopic c₀ (Quotient.out (X.cls c₀ α)).1 α :=
    (cls_eq_iff hα₀ hα).mp (cls_out _)
  have hend : galleryEnd c₀ (Quotient.out (X.cls c₀ α)).1 = galleryEnd c₀ α := h₀.galleryEnd_eq
  have hex : ∃ ρ', X.IsReducedOrdinary cs (galleryEnd c₀ (Quotient.out (X.cls c₀ α)).1) ρ' ∧
      X.cls c₀ ((Quotient.out (X.cls c₀ α)).1 ++ ρ') = X.cls c₀ (α ++ ρ) :=
    ⟨ρ, hend ▸ hρ, cls_congr (h₀.append_right ρ)⟩
  rw [coverDist, dite_eq_left hex]
  obtain ⟨h1, h2⟩ := hex.choose_spec
  have h4 : X.TwoHomotopic c₀ ((Quotient.out (X.cls c₀ α)).1 ++ hex.choose)
      ((Quotient.out (X.cls c₀ α)).1 ++ ρ) := by
    rw [← cls_eq_iff (hα₀.append h1.1.isGallery) (hα₀.append (hend ▸ hρ).1.isGallery), h2]
    exact cls_congr (h₀.append_right ρ).symm
  have h5 := twoHomotopic_of_append_left hα₀ h4
  exact (strictHomotopic_of_twoHomotopic' hres h3 h1 (hend ▸ hρ) h5).wordProd_eq

theorem coverDist_eq_one_iff (A B : X.Cover c₀) : X.coverDist cs c₀ A B = 1 ↔ A = B := by
  obtain ⟨α, hα, rfl⟩ := exists_eq_cls A
  obtain ⟨ρ, hρ, rfl⟩ := exists_cls_append hres hα B
  rw [coverDist_cls_append hres h3 hα hρ]
  constructor
  · intro h
    have hl := hρ.2.eq
    rw [h, cs.length_one] at hl
    have hnil : ρ = [] := List.length_eq_zero_iff.mp (by simpa using hl.symm)
    subst hnil
    simp
  · intro h
    have h1 := (cls_eq_iff hα (hα.append hρ.1.isGallery)).mp h
    have h2 : X.TwoHomotopic (galleryEnd c₀ α) ρ [] :=
      twoHomotopic_of_append_left hα (by simpa using h1.symm)
    rw [(strictHomotopic_of_twoHomotopic' hres h3 hρ (IsReducedOrdinary.nil _) h2).wordProd_eq]
    simp

theorem universalCover_adj_iff (i : ι) (A B : X.Cover c₀) :
    (X.universalCover c₀).adj i A B ↔
      X.coverDist cs c₀ A B = 1 ∨ X.coverDist cs c₀ A B = cs.simple i := by
  obtain ⟨α, hα, rfl⟩ := exists_eq_cls A
  constructor
  · intro h
    obtain ⟨y, hy, rfl⟩ := (universalCover_adj_cls_iff hα).mp h
    by_cases hye : y = galleryEnd c₀ α
    · left
      rw [coverDist_eq_one_iff hres h3]
      subst hye
      have := twoHomotopic_constant (X := X) (x := c₀) α [] i
      simp only [List.append_nil] at this
      exact (cls_congr this).symm
    · right
      rw [coverDist_cls_append hres h3 hα (isReducedOrdinary_singleton hy (Ne.symm hye))]
      simp
  · rintro (h | h)
    · rw [coverDist_eq_one_iff hres h3] at h
      rw [← h]
      exact (X.universalCover c₀).adj_refl i _
    · obtain ⟨ρ, hρ, rfl⟩ := exists_cls_append hres hα B
      rw [coverDist_cls_append hres h3 hα hρ] at h
      have hlen : (galleryType ρ).length = 1 := by rw [← hρ.2.eq, h, cs.length_simple]
      obtain ⟨⟨j, y⟩, rfl⟩ := List.length_eq_one_iff.mp (by simpa using hlen)
      have hj : j = i := cs.simple_injective (by simpa using h)
      subst hj
      exact (universalCover_adj_cls_iff hα).mpr ⟨y, hρ.1.1, rfl⟩

theorem exists_eq_cls_of_coverDist_eq_simple {α ρ : List (ι × C)} (hα : X.IsGallery c₀ α)
    (hρ : X.IsReducedOrdinary cs (galleryEnd c₀ α) ρ) {B' : X.Cover c₀} {i : ι}
    (h : X.coverDist cs c₀ (X.cls c₀ (α ++ ρ)) B' = cs.simple i) :
    ∃ y, X.adj i (galleryEnd c₀ (α ++ ρ)) y ∧ y ≠ galleryEnd c₀ (α ++ ρ) ∧
      B' = X.cls c₀ (α ++ ρ ++ [(i, y)]) := by
  have hαρ : X.IsGallery c₀ (α ++ ρ) := hα.append hρ.1.isGallery
  obtain ⟨y, hy, rfl⟩ := (universalCover_adj_cls_iff hαρ).mp
    ((universalCover_adj_iff hres h3 i _ _).mpr (Or.inr h))
  refine ⟨y, hy, fun hye => ?_, rfl⟩
  have hc := twoHomotopic_constant (X := X) (x := c₀) (α ++ ρ) [] i
  simp only [List.append_nil] at hc
  rw [← hye] at hc
  rw [← cls_congr hc, (coverDist_eq_one_iff hres h3 _ _).mpr rfl] at h
  exact cs.simple_ne_one i h.symm

theorem coverDist_mul_simple (A B B' : X.Cover c₀) (i : ι)
    (h : X.coverDist cs c₀ B B' = cs.simple i) :
    (X.coverDist cs c₀ A B' = X.coverDist cs c₀ A B ∨
      X.coverDist cs c₀ A B' = X.coverDist cs c₀ A B * cs.simple i) ∧
    (cs.length (X.coverDist cs c₀ A B * cs.simple i) = cs.length (X.coverDist cs c₀ A B) + 1 →
      X.coverDist cs c₀ A B' = X.coverDist cs c₀ A B * cs.simple i) := by
  obtain ⟨α, hα, rfl⟩ := exists_eq_cls A
  obtain ⟨ρ, hρ, rfl⟩ := exists_cls_append hres hα B
  obtain ⟨y, hy, hye, rfl⟩ := exists_eq_cls_of_coverDist_eq_simple hres h3 hα hρ h
  rw [coverDist_cls_append hres h3 hα hρ]
  rw [galleryEnd_append] at hy hye
  rcases cs.length_mul_simple (cs.wordProd (galleryType ρ)) i with h1 | h1
  · have hρy : X.IsReducedOrdinary cs (galleryEnd c₀ α) (ρ ++ [(i, y)]) := by
      refine ⟨(isOrdinary_concat _ ρ (i, y)).mpr ⟨hρ.1, hy, Ne.symm hye⟩, ?_⟩
      rw [CoxeterSystem.IsReduced, galleryType_append, cs.wordProd_append]
      simp [h1, hρ.2.eq]
    rw [List.append_assoc, coverDist_cls_append hres h3 hα hρy]
    have e : cs.wordProd (galleryType (ρ ++ [(i, y)])) =
        cs.wordProd (galleryType ρ) * cs.simple i := by
      simp [galleryType_append, cs.wordProd_append]
    exact ⟨Or.inr e, fun _ => e⟩
  · obtain ⟨ρ₁, z, h2⟩ := exists_strictHomotopic_concat hres hρ h1
    have hρ₁z := h2.isReducedOrdinary_iff.mp hρ
    have hρ₁ := hρ₁z.of_append_left
    have hz : galleryEnd (galleryEnd c₀ α) ρ = z := by rw [h2.galleryEnd_eq, galleryEnd_concat]
    obtain ⟨-, hz1, hz2⟩ := (isOrdinary_concat _ ρ₁ (i, z)).mp hρ₁z.1
    have hval : cs.wordProd (galleryType ρ₁) * cs.simple i = cs.wordProd (galleryType ρ) := by
      rw [h2.wordProd_eq]
      simp [galleryType_append, cs.wordProd_append]
    have hB : X.cls c₀ (α ++ ρ ++ [(i, y)]) = X.cls c₀ (α ++ ρ₁ ++ [(i, z), (i, y)]) := by
      have := ((h2.twoHomotopic).append_left (x := c₀) α).append_right [(i, y)]
      rw [cls_congr this]
      simp
    have hzy : X.adj i z y := hz ▸ hy
    refine ⟨?_, fun h4 => by omega⟩
    by_cases hy₁ : y = galleryEnd c₀ (α ++ ρ₁)
    · right
      have hb := twoHomotopic_backtrack (X := X) (x := c₀) (α ++ ρ₁) [] (i := i) (y := z)
        (by rw [galleryEnd_append]; exact hz1)
      simp only [List.append_nil] at hb
      rw [hB, hy₁, cls_congr hb, coverDist_cls_append hres h3 hα hρ₁, ← hval, mul_assoc,
        cs.simple_mul_simple_self, mul_one]
    · left
      have hp := twoHomotopic_panel (X := X) (x := c₀) (α ++ ρ₁) [] (i := i) (y := z) (z := y)
        (by rw [galleryEnd_append]; exact hz1) hzy
      simp only [List.append_nil] at hp
      rw [galleryEnd_append] at hy₁
      have hρ₁y : X.IsReducedOrdinary cs (galleryEnd c₀ α) (ρ₁ ++ [(i, y)]) := by
        refine ⟨(isOrdinary_concat _ ρ₁ (i, y)).mpr ⟨hρ₁.1, adj_trans hz1 hzy, Ne.symm hy₁⟩, ?_⟩
        have := hρ₁z.2
        simpa [galleryType_append] using this
      rw [hB, cls_congr hp, List.append_assoc, coverDist_cls_append hres h3 hα hρ₁y,
        h2.wordProd_eq]
      simp [galleryType_append]

theorem coverDist_exists_simple (hpanel : ∀ (i : ι) (x : C), ∃ y, y ≠ x ∧ X.adj i x y)
    (A B : X.Cover c₀) (i : ι) :
    ∃ B', X.coverDist cs c₀ B B' = cs.simple i ∧
      X.coverDist cs c₀ A B' = X.coverDist cs c₀ A B * cs.simple i := by
  obtain ⟨α, hα, rfl⟩ := exists_eq_cls A
  obtain ⟨ρ, hρ, rfl⟩ := exists_cls_append hres hα B
  have hαρ : X.IsGallery c₀ (α ++ ρ) := hα.append hρ.1.isGallery
  rw [coverDist_cls_append hres h3 hα hρ]
  rcases cs.length_mul_simple (cs.wordProd (galleryType ρ)) i with h1 | h1
  · obtain ⟨y, hy, hadj⟩ := hpanel i (galleryEnd c₀ (α ++ ρ))
    refine ⟨X.cls c₀ (α ++ ρ ++ [(i, y)]), ?_, ?_⟩
    · rw [coverDist_cls_append hres h3 hαρ (isReducedOrdinary_singleton hadj (Ne.symm hy))]
      simp
    · rw [galleryEnd_append] at hy hadj
      have hρy : X.IsReducedOrdinary cs (galleryEnd c₀ α) (ρ ++ [(i, y)]) := by
        refine ⟨(isOrdinary_concat _ ρ (i, y)).mpr ⟨hρ.1, hadj, Ne.symm hy⟩, ?_⟩
        rw [CoxeterSystem.IsReduced, galleryType_append, cs.wordProd_append]
        simp [h1, hρ.2.eq]
      rw [List.append_assoc, coverDist_cls_append hres h3 hα hρy]
      simp [galleryType_append, cs.wordProd_append]
  · obtain ⟨ρ₁, z, h2⟩ := exists_strictHomotopic_concat hres hρ h1
    have hρ₁z := h2.isReducedOrdinary_iff.mp hρ
    have hρ₁ := hρ₁z.of_append_left
    obtain ⟨-, hz1, hz2⟩ := (isOrdinary_concat _ ρ₁ (i, z)).mp hρ₁z.1
    have hval : cs.wordProd (galleryType ρ₁) * cs.simple i = cs.wordProd (galleryType ρ) := by
      rw [h2.wordProd_eq]
      simp [galleryType_append, cs.wordProd_append]
    refine ⟨X.cls c₀ (α ++ ρ₁), ?_, ?_⟩
    · have hαρ₁ : X.IsGallery c₀ (α ++ ρ₁) := hα.append hρ₁.1.isGallery
      have hB : X.cls c₀ (α ++ ρ) = X.cls c₀ (α ++ ρ₁ ++ [(i, z)]) := by
        rw [List.append_assoc]
        exact cls_congr ((h2.twoHomotopic).append_left (x := c₀) α)
      have h5 : X.coverDist cs c₀ (X.cls c₀ (α ++ ρ₁)) (X.cls c₀ (α ++ ρ)) = cs.simple i := by
        rw [hB, coverDist_cls_append hres h3 hαρ₁ (isReducedOrdinary_singleton
          (by rw [galleryEnd_append]; exact hz1) (by rw [galleryEnd_append]; exact hz2))]
        simp
      have h6 := (universalCover_adj_iff hres h3 i _ _).mpr (Or.inr h5)
      rcases (universalCover_adj_iff hres h3 i _ _).mp (coverAdj_symm h6) with h7 | h7
      · rw [coverDist_eq_one_iff hres h3] at h7
        rw [h7, (coverDist_eq_one_iff hres h3 _ _).mpr rfl] at h5
        exact absurd h5.symm (cs.simple_ne_one i)
      · exact h7
    · rw [coverDist_cls_append hres h3 hα hρ₁, ← hval, mul_assoc, cs.simple_mul_simple_self,
        mul_one]

theorem isWeylDistanceBuilding_coverDist (hpanel : ∀ (i : ι) (x : C), ∃ y, y ≠ x ∧ X.adj i x y) :
    IsWeylDistanceBuilding cs (X.coverDist cs c₀) where
  nonempty := ⟨X.coverBase c₀⟩
  eq_one_iff := coverDist_eq_one_iff hres h3
  mul_simple A B B' i h := coverDist_mul_simple hres h3 A B B' i h
  exists_simple A B i := coverDist_exists_simple hres h3 hpanel A B i

end ChamberSystem

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley ChamberSystem

theorem F4_rank_three_local_building_cover
    {C : Type*} (X : ChamberSystem (Fin Tag.F4.rank) C)
    (c₀ : C) (hpanel : ∀ (i : Fin Tag.F4.rank) (x : C), ∃ y, y ≠ x ∧ X.adj i x y)
    (hres2 : ∀ J : Set (Fin Tag.F4.rank), J.ncard = 2 → ∀ x,
      X.IsResidueBuilding (coxeterSystem .F4) J x)
    (hres3 : ∀ J : Set (Fin Tag.F4.rank), J.ncard = 3 → ∀ x,
      X.IsResidueBuilding (coxeterSystem .F4) J x) :
    ∃ δ : X.Cover c₀ → X.Cover c₀ → WeylGroup .F4,
      IsWeylDistanceBuilding (coxeterSystem .F4) δ ∧
      (∀ (i : Fin Tag.F4.rank) (A B : X.Cover c₀), (X.universalCover c₀).adj i A B ↔
        δ A B = 1 ∨ δ A B = (coxeterSystem .F4).simple i) ∧
      (∀ (i : Fin Tag.F4.rank) (A : X.Cover c₀),
        (panel (coxeterSystem .F4) δ i A).encard = (X.residue {i} (X.coverProj c₀ A)).encard) ∧
      ∀ (i : Fin Tag.F4.rank) (A : X.Cover c₀),
        ((X.universalCover c₀).residue {i} A).encard =
          (X.residue {i} (X.coverProj c₀ A)).encard := by
  have : Nontrivial (Fin Tag.F4.rank) := Fin.nontrivial_iff_two_le.mpr (by decide)
  have hres : ∀ s t : Fin Tag.F4.rank, s ≠ t → ∀ y : C,
      X.IsResidueBuilding (coxeterSystem .F4) {s, t} y := fun s t hst y =>
    hres2 {s, t} (Set.ncard_pair hst) y
  have h3 : ∀ T : Finset (Fin Tag.F4.rank), T.card ≤ 3 → ∀ y : C,
      ∃ T' : Set (Fin Tag.F4.rank), (T : Set _) ⊆ T' ∧
        X.IsResidueBuilding (coxeterSystem .F4) T' y := by
    intro T hT y
    have huniv : (Set.univ : Set (Fin Tag.F4.rank)).encard = 4 := by
      rw [Set.encard_univ, ENat.card_eq_coe_fintype_card, Fintype.card_fin]
      rfl
    have hTc : (T : Set (Fin Tag.F4.rank)).encard ≤ 3 := by
      rw [Set.encard_coe_eq_coe_finsetCard]
      exact_mod_cast hT
    obtain ⟨T', hTT', -, hT'⟩ := Set.exists_superset_subset_encard_eq (k := 3)
      (Set.subset_univ (T : Set (Fin Tag.F4.rank))) hTc (by rw [huniv]; norm_num)
    refine ⟨T', hTT', hres3 T' ?_ y⟩
    rw [Set.ncard, hT']
    rfl
  have hδ := isWeylDistanceBuilding_coverDist (c₀ := c₀) hres h3 hpanel
  have hpan : ∀ i A, ((X.universalCover c₀).residue {i} A).encard =
      (X.residue {i} (X.coverProj c₀ A)).encard := fun i A => by
    rw [← (bijOn_coverProj_panel i A).image_eq, (bijOn_coverProj_panel i A).injOn.encard_image]
  refine ⟨X.coverDist (coxeterSystem .F4) c₀, hδ, universalCover_adj_iff hres h3, fun i A => ?_,
    hpan⟩
  rw [← hpan]
  congr 1
  ext B
  rw [mem_panel_iff hδ, mem_residue_singleton, universalCover_adj_iff hres h3]

end CFSG.Monster.B.Geometry
