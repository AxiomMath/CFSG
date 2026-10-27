module

public import CFSG.Blueprint.Chevalley

public section

namespace CFSG.Quasithin.G2U

open CFSG.Blueprint.Chevalley

@[expose] def vec (a b : ℤ) : Fin Tag.G2.rank → ℤ :=
  ![a, b]

@[expose] def ix (n : Fin 2) : Fin Tag.G2.rank :=
  n

@[expose] def rootList : List (Fin Tag.G2.rank → ℤ) :=
  [vec 2 3, vec 1 3, vec 1 2, vec 1 1, vec 0 1, vec 1 0, vec (-1) 0, vec 0 (-1), vec (-1) (-1),
    vec (-1) (-2), vec (-1) (-3), vec (-2) (-3)]

theorem reflect_mem_rootList : ∀ v ∈ rootList, ∀ i, reflect .G2 i v ∈ rootList := by
  decide

theorem single_mem_rootList : ∀ j : Fin Tag.G2.rank, Pi.single j 1 ∈ rootList := by
  decide

theorem mem_rootList_of_isRoot {v : Fin Tag.G2.rank → ℤ} (h : IsRoot .G2 v) : v ∈ rootList := by
  induction h with
  | basis j => exact single_mem_rootList j
  | reflect i _ ih => exact reflect_mem_rootList _ ih i

private theorem isRoot_congr {v w : Fin Tag.G2.rank → ℤ} (h : IsRoot .G2 v) (e : v = w) :
    IsRoot .G2 w :=
  e ▸ h

theorem isRoot_10 : IsRoot .G2 (vec 1 0) := isRoot_congr (.basis (ix 0)) (by decide)

theorem isRoot_01 : IsRoot .G2 (vec 0 1) := isRoot_congr (.basis (ix 1)) (by decide)

theorem isRoot_11 : IsRoot .G2 (vec 1 1) := isRoot_congr (.reflect (ix 0) isRoot_01) (by decide)

theorem isRoot_13 : IsRoot .G2 (vec 1 3) := isRoot_congr (.reflect (ix 1) isRoot_10) (by decide)

theorem isRoot_12 : IsRoot .G2 (vec 1 2) := isRoot_congr (.reflect (ix 1) isRoot_11) (by decide)

theorem isRoot_23 : IsRoot .G2 (vec 2 3) := isRoot_congr (.reflect (ix 0) isRoot_13) (by decide)

theorem isRoot_n10 : IsRoot .G2 (vec (-1) 0) :=
  isRoot_congr (.reflect (ix 0) isRoot_10) (by decide)

theorem isRoot_n01 : IsRoot .G2 (vec 0 (-1)) :=
  isRoot_congr (.reflect (ix 1) isRoot_01) (by decide)

theorem isRoot_n11 : IsRoot .G2 (vec (-1) (-1)) :=
  isRoot_congr (.reflect (ix 0) isRoot_n01) (by decide)

theorem isRoot_n13 : IsRoot .G2 (vec (-1) (-3)) :=
  isRoot_congr (.reflect (ix 1) isRoot_n10) (by decide)

theorem isRoot_n12 : IsRoot .G2 (vec (-1) (-2)) :=
  isRoot_congr (.reflect (ix 1) isRoot_n11) (by decide)

theorem isRoot_n23 : IsRoot .G2 (vec (-2) (-3)) :=
  isRoot_congr (.reflect (ix 0) isRoot_n13) (by decide)

theorem isRoot_of_mem_rootList {v : Fin Tag.G2.rank → ℤ} (hv : v ∈ rootList) : IsRoot .G2 v := by
  simp only [rootList, List.mem_cons, List.not_mem_nil, or_false] at hv
  rcases hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  exacts [isRoot_23, isRoot_13, isRoot_12, isRoot_11, isRoot_01, isRoot_10, isRoot_n10,
    isRoot_n01, isRoot_n11, isRoot_n12, isRoot_n13, isRoot_n23]

theorem isRoot_iff_mem_rootList {v : Fin Tag.G2.rank → ℤ} : IsRoot .G2 v ↔ v ∈ rootList :=
  ⟨mem_rootList_of_isRoot, isRoot_of_mem_rootList⟩

@[expose] def su (i : Fin Tag.G2.rank) (α : Fin Tag.G2.rank → ℤ) : ℕ :=
  ((List.range 7).filter fun k : ℕ => decide (α + (k : ℤ) • Pi.single i 1 ∈ rootList)).foldr
    max 0

@[expose] def sd (i : Fin Tag.G2.rank) (α : Fin Tag.G2.rank → ℤ) : ℕ :=
  ((List.range 7).filter fun k : ℕ => decide (α - (k : ℤ) • Pi.single i 1 ∈ rootList)).foldr
    max 0

private theorem coord_le : ∀ v ∈ rootList, ∀ j, v j ≤ 3 := by
  decide

private theorem coord_ge : ∀ v ∈ rootList, ∀ j, -3 ≤ v j := by
  decide

private theorem su_mem :
    ∀ α ∈ rootList, ∀ i, α + ((su i α : ℕ) : ℤ) • Pi.single i 1 ∈ rootList := by
  decide

private theorem su_max : ∀ α ∈ rootList, ∀ i, ∀ k < 7,
    α + ((k : ℕ) : ℤ) • Pi.single i 1 ∈ rootList → k ≤ su i α := by
  decide

private theorem sd_mem :
    ∀ α ∈ rootList, ∀ i, α - ((sd i α : ℕ) : ℤ) • Pi.single i 1 ∈ rootList := by
  decide

private theorem sd_max : ∀ α ∈ rootList, ∀ i, ∀ k < 7,
    α - ((k : ℕ) : ℤ) • Pi.single i 1 ∈ rootList → k ≤ sd i α := by
  decide

theorem stringUp_eq {i : Fin Tag.G2.rank} {α : Fin Tag.G2.rank → ℤ} (hα : IsRoot .G2 α) :
    stringUp .G2 i α = su i α := by
  have hα' := mem_rootList_of_isRoot hα
  refine IsGreatest.csSup_eq ⟨isRoot_of_mem_rootList (su_mem α hα' i), fun k hk => ?_⟩
  have hk' := mem_rootList_of_isRoot hk
  by_contra! hlt
  by_cases h7 : k < 7
  · exact absurd (su_max α hα' i k h7 hk') (not_le.mpr hlt)
  · have h1 := coord_le _ hk' i
    have h2 := coord_ge α hα' i
    simp only [Pi.add_apply, Pi.smul_apply, Pi.single_eq_same, smul_eq_mul, mul_one] at h1
    omega

theorem stringDown_eq {i : Fin Tag.G2.rank} {α : Fin Tag.G2.rank → ℤ} (hα : IsRoot .G2 α) :
    stringDown .G2 i α = sd i α := by
  have hα' := mem_rootList_of_isRoot hα
  refine IsGreatest.csSup_eq ⟨isRoot_of_mem_rootList (sd_mem α hα' i), fun k hk => ?_⟩
  have hk' := mem_rootList_of_isRoot hk
  by_contra! hlt
  by_cases h7 : k < 7
  · exact absurd (sd_max α hα' i k h7 hk') (not_le.mpr hlt)
  · have h1 := coord_ge _ hk' i
    have h2 := coord_le α hα' i
    simp only [Pi.sub_apply, Pi.smul_apply, Pi.single_eq_same, smul_eq_mul, mul_one] at h1
    omega

@[expose] def lab : Fin 14 → Label .G2 :=
  ![.inr ⟨vec 2 3, isRoot_23⟩, .inr ⟨vec 1 3, isRoot_13⟩, .inr ⟨vec 1 2, isRoot_12⟩,
    .inr ⟨vec 1 1, isRoot_11⟩, .inr ⟨vec 0 1, isRoot_01⟩, .inr ⟨vec 1 0, isRoot_10⟩,
    .inl (ix 0), .inl (ix 1), .inr ⟨vec (-1) 0, isRoot_n10⟩, .inr ⟨vec 0 (-1), isRoot_n01⟩,
    .inr ⟨vec (-1) (-1), isRoot_n11⟩, .inr ⟨vec (-1) (-2), isRoot_n12⟩,
    .inr ⟨vec (-1) (-3), isRoot_n13⟩, .inr ⟨vec (-2) (-3), isRoot_n23⟩]

theorem lab_injective : Function.Injective lab := by
  have h : ∀ a b, lab a = lab b → a = b := by decide
  exact fun a b => h a b

theorem lab_surjective : Function.Surjective lab := by
  rintro (j | ⟨v, hv⟩)
  · have h : ∀ j : Fin Tag.G2.rank, ∃ b, lab b = .inl j := by decide
    exact h j
  · have hv' := mem_rootList_of_isRoot hv
    simp only [rootList, List.mem_cons, List.not_mem_nil, or_false] at hv'
    rcases hv' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [⟨0, rfl⟩, ⟨1, rfl⟩, ⟨2, rfl⟩, ⟨3, rfl⟩, ⟨4, rfl⟩, ⟨5, rfl⟩, ⟨8, rfl⟩, ⟨9, rfl⟩,
      ⟨10, rfl⟩, ⟨11, rfl⟩, ⟨12, rfl⟩, ⟨13, rfl⟩]

@[expose] noncomputable def bas : Fin 14 ≃ Label .G2 :=
  Equiv.ofBijective lab ⟨lab_injective, lab_surjective⟩

theorem bas_apply (b : Fin 14) : bas b = lab b :=
  rfl

end CFSG.Quasithin.G2U
