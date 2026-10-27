module

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239PairsLieG2Facts

public section

namespace CFSG.Quasithin.H13.F431.G2.Cent

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.QuasithinUnique.Vol2Native.L239.Lie.G2
open scoped commutatorElement

section Spans

set_option linter.unusedSectionVars false


@[expose] def TC : Set (Fin Tag.G2.rank → ℤ) := {rC}

@[expose] def TBC : Set (Fin Tag.G2.rank → ℤ) := {rB, rC}

@[expose] def TVBC : Set (Fin Tag.G2.rank → ℤ) := {rV, rB, rC}

theorem eq_rC_of_first_coord {γ : Fin Tag.G2.rank → ℤ} (h : IsRoot Tag.G2 γ) (hp : 0 < height γ)
    (h2 : 2 ≤ γ i0) : γ = rC := by
  rcases isRoot_pos_iff.1 ⟨h, hp⟩ with rfl | rfl | rfl | rfl | rfl | rfl <;>
    first | rfl | (exfalso; revert h2; decide)

theorem closed_of_rC_mem {T : Set (Fin Tag.G2.rank → ℤ)}
    (hpos : ∀ α ∈ T, IsRoot Tag.G2 α ∧ 0 < height α) (h1 : ∀ α ∈ T, 1 ≤ α i0) (hc : rC ∈ T) :
    ∀ α ∈ T, ∀ β ∈ T, ∀ a b : ℕ, 1 ≤ a → 1 ≤ b → IsRoot Tag.G2 (a • α + b • β) →
      a • α + b • β ∈ T := by
  intro α hα β hβ a b ha hb hr
  have ha' : (1 : ℤ) ≤ a := by exact_mod_cast ha
  have hb' : (1 : ℤ) ≤ b := by exact_mod_cast hb
  have hpos' : 0 < height (a • α + b • β) := by
    rw [height_nsmul_add_nsmul]
    have h1' := (hpos α hα).2
    have h2' := (hpos β hβ).2
    nlinarith
  have h2 : 2 ≤ (a • α + b • β) i0 := by
    have e : (a • α + b • β) i0 = (a : ℤ) * α i0 + (b : ℤ) * β i0 := by
      simp
    rw [e]
    have h1' := h1 α hα
    have h2' := h1 β hβ
    nlinarith
  rw [eq_rC_of_first_coord hr hpos' h2]
  exact hc

theorem pos_TC : ∀ α ∈ TC, IsRoot Tag.G2 α ∧ 0 < height α := by
  intro α hα
  rw [TC, Set.mem_singleton_iff] at hα
  subst hα
  exact isRoot_pos_iff.2 (by simp)

theorem pos_TBC : ∀ α ∈ TBC, IsRoot Tag.G2 α ∧ 0 < height α := by
  intro α hα
  rcases hα with rfl | rfl <;> exact isRoot_pos_iff.2 (by simp)

theorem pos_TVBC : ∀ α ∈ TVBC, IsRoot Tag.G2 α ∧ 0 < height α := by
  intro α hα
  rcases hα with rfl | rfl | rfl <;> exact isRoot_pos_iff.2 (by simp)

theorem closed_TC : ∀ α ∈ TC, ∀ β ∈ TC, ∀ a b : ℕ, 1 ≤ a → 1 ≤ b →
    IsRoot Tag.G2 (a • α + b • β) → a • α + b • β ∈ TC :=
  closed_of_rC_mem pos_TC (fun α hα => by
    rw [TC, Set.mem_singleton_iff] at hα
    subst hα
    decide) (Set.mem_singleton _)

theorem closed_TBC : ∀ α ∈ TBC, ∀ β ∈ TBC, ∀ a b : ℕ, 1 ≤ a → 1 ≤ b →
    IsRoot Tag.G2 (a • α + b • β) → a • α + b • β ∈ TBC :=
  closed_of_rC_mem pos_TBC (fun α hα => by
    rcases hα with rfl | rfl <;> decide) (Or.inr rfl)

theorem closed_TVBC : ∀ α ∈ TVBC, ∀ β ∈ TVBC, ∀ a b : ℕ, 1 ≤ a → 1 ≤ b →
    IsRoot Tag.G2 (a • α + b • β) → a • α + b • β ∈ TVBC :=
  closed_of_rC_mem pos_TVBC (fun α hα => by
    rcases hα with rfl | rfl | rfl <;> decide) (Or.inr (Or.inr rfl))

end Spans

section Normalizers

set_option linter.unusedSectionVars false


variable {K : Type} [Field K] [CharP K 2]

theorem radicalRootsGe_one_five :
    parabolicRadicalRootsGe Tag.G2 ({i1} : Set (Fin Tag.G2.rank)) 5 = TC := by
  ext α
  simp only [parabolicRadicalRootsGe, Set.mem_ofPred_eq, radicalRoots_one, TC,
    Set.mem_singleton_iff, Set.mem_insert_iff]
  constructor
  · rintro ⟨h | h | h | h | h, h5⟩ <;> subst h <;> first | rfl | (exfalso; revert h5; decide)
  · rintro rfl
    exact ⟨Or.inr (Or.inr (Or.inr (Or.inr rfl))), by decide⟩

theorem radicalRootsGe_zero_four :
    parabolicRadicalRootsGe Tag.G2 ({i0} : Set (Fin Tag.G2.rank)) 4 = TBC := by
  ext α
  simp only [parabolicRadicalRootsGe, Set.mem_ofPred_eq, radicalRoots_zero, TBC,
    Set.mem_singleton_iff, Set.mem_insert_iff]
  constructor
  · rintro ⟨h | h | h | h | h, h5⟩ <;> subst h <;>
      first | exact Or.inl rfl | exact Or.inr rfl | (exfalso; revert h5; decide)
  · rintro (rfl | rfl)
    · exact ⟨Or.inr (Or.inr (Or.inr (Or.inl rfl))), by decide⟩
    · exact ⟨Or.inr (Or.inr (Or.inr (Or.inr rfl))), by decide⟩

theorem radicalRootsGe_zero_three :
    parabolicRadicalRootsGe Tag.G2 ({i0} : Set (Fin Tag.G2.rank)) 3 = TVBC := by
  ext α
  simp only [parabolicRadicalRootsGe, Set.mem_ofPred_eq, radicalRoots_zero, TVBC,
    Set.mem_singleton_iff, Set.mem_insert_iff]
  constructor
  · rintro ⟨h | h | h | h | h, h5⟩ <;> subst h <;>
      first | exact Or.inl rfl | exact Or.inr (Or.inl rfl) | exact Or.inr (Or.inr rfl) |
        (exfalso; revert h5; decide)
  · rintro (rfl | rfl | rfl)
    · exact ⟨Or.inr (Or.inr (Or.inl rfl)), by decide⟩
    · exact ⟨Or.inr (Or.inr (Or.inr (Or.inl rfl))), by decide⟩
    · exact ⟨Or.inr (Or.inr (Or.inr (Or.inr rfl))), by decide⟩

theorem borel_le_normalizer_TC :
    borelGroup Tag.G2 K ≤ Subgroup.normalizer (rootSpan Tag.G2 K TC : Set (ModGL Tag.G2 K)) := by
  have h := borelGroup_le_normalizer_parabolicRadicalGe (K := K) ({i1} : Set (Fin Tag.G2.rank)) 5
  rwa [parabolicRadicalGe, radicalRootsGe_one_five] at h

theorem borel_le_normalizer_TBC :
    borelGroup Tag.G2 K ≤ Subgroup.normalizer (rootSpan Tag.G2 K TBC : Set (ModGL Tag.G2 K)) := by
  have h := borelGroup_le_normalizer_parabolicRadicalGe (K := K) ({i0} : Set (Fin Tag.G2.rank)) 4
  rwa [parabolicRadicalGe, radicalRootsGe_zero_four] at h

theorem borel_le_normalizer_TVBC :
    borelGroup Tag.G2 K ≤ Subgroup.normalizer (rootSpan Tag.G2 K TVBC : Set (ModGL Tag.G2 K)) := by
  have h := borelGroup_le_normalizer_parabolicRadicalGe (K := K) ({i0} : Set (Fin Tag.G2.rank)) 3
  rwa [parabolicRadicalGe, radicalRootsGe_zero_three] at h

theorem reflect_a_v : reflect Tag.G2 i0 rV = rV := List.ofFn_injective (by decide +kernel)

theorem reflect_a_b' : reflect Tag.G2 i0 rB = rC := List.ofFn_injective (by decide +kernel)

theorem reflect_a_c' : reflect Tag.G2 i0 rC = rB := List.ofFn_injective (by decide +kernel)

theorem reflect_image_TBC : reflect Tag.G2 i0 '' TBC = TBC := by
  ext α
  simp only [TBC, Set.image_insert_eq, Set.image_singleton, Set.mem_insert_iff,
    Set.mem_singleton_iff, reflect_a_b', reflect_a_c']
  tauto

theorem reflect_image_TVBC : reflect Tag.G2 i0 '' TVBC = TVBC := by
  ext α
  simp only [TVBC, Set.image_insert_eq, Set.image_singleton, Set.mem_insert_iff,
    Set.mem_singleton_iff, reflect_a_v, reflect_a_b', reflect_a_c']
  tauto

theorem weylElt_a_mem_normalizer_TBC : weylElt Tag.G2 K i0 1 ∈
    Subgroup.normalizer (rootSpan Tag.G2 K TBC : Set (ModGL Tag.G2 K)) := by
  refine mem_normalizer_of_map_eq ?_
  rw [map_conj_weylElt_rootSpan K i0 1 (fun α hα => (pos_TBC α hα).1), reflect_image_TBC]

theorem weylElt_a_mem_normalizer_TVBC : weylElt Tag.G2 K i0 1 ∈
    Subgroup.normalizer (rootSpan Tag.G2 K TVBC : Set (ModGL Tag.G2 K)) := by
  refine mem_normalizer_of_map_eq ?_
  rw [map_conj_weylElt_rootSpan K i0 1 (fun α hα => (pos_TVBC α hα).1), reflect_image_TVBC]

theorem parabolic_a_le_normalizer_TBC :
    parabolicSubgroup Tag.G2 K {i0} ≤
      Subgroup.normalizer (rootSpan Tag.G2 K TBC : Set (ModGL Tag.G2 K)) :=
  sup_le borel_le_normalizer_TBC ((Subgroup.closure_le _).2 (by
    rintro _ ⟨j, hj, rfl⟩
    rw [Set.mem_singleton_iff.1 hj]
    exact weylElt_a_mem_normalizer_TBC))

theorem parabolic_a_le_normalizer_TVBC :
    parabolicSubgroup Tag.G2 K {i0} ≤
      Subgroup.normalizer (rootSpan Tag.G2 K TVBC : Set (ModGL Tag.G2 K)) :=
  sup_le borel_le_normalizer_TVBC ((Subgroup.closure_le _).2 (by
    rintro _ ⟨j, hj, rfl⟩
    rw [Set.mem_singleton_iff.1 hj]
    exact weylElt_a_mem_normalizer_TVBC))

end Normalizers

section NormalForms

set_option linter.unusedSectionVars false


variable {K : Type} [Field K] [CharP K 2]

theorem mem_rootSpan_TC_iff {y : ModGL Tag.G2 K} :
    y ∈ rootSpan Tag.G2 K TC ↔ ∃ s : K, y = gX rC s := by
  constructor
  · intro hy
    have hinj : Function.Injective ![rC] := by decide
    have hrange : Set.range ![rC] = TC := by
      ext α; simp [TC]
    obtain ⟨c, -, hc⟩ := (bijOn_prod_pinnedX K pos_TC closed_TC ![rC] hinj hrange).surjOn hy
    refine ⟨c 0, ?_⟩
    rw [← hc]
    simp [List.ofFn_succ, gX]
  · rintro ⟨s, rfl⟩
    exact pinnedX_mem_rootSpan (show rC ∈ TC from Set.mem_singleton _) s

theorem mem_rootSpan_TBC_iff {y : ModGL Tag.G2 K} :
    y ∈ rootSpan Tag.G2 K TBC ↔ ∃ β γ : K, y = gX rB β * gX rC γ := by
  constructor
  · intro hy
    have hinj : Function.Injective ![rB, rC] := by decide
    have hrange : Set.range ![rB, rC] = TBC := by
      ext α; simp [TBC]; tauto
    obtain ⟨c, -, hc⟩ := (bijOn_prod_pinnedX K pos_TBC closed_TBC ![rB, rC] hinj hrange).surjOn hy
    refine ⟨c 0, c 1, ?_⟩
    rw [← hc]
    simp [List.ofFn_succ, gX]
  · rintro ⟨β, γ, rfl⟩
    exact (rootSpan Tag.G2 K TBC).mul_mem
      (pinnedX_mem_rootSpan (show rB ∈ TBC from Or.inl rfl) β)
      (pinnedX_mem_rootSpan (show rC ∈ TBC from Or.inr rfl) γ)

theorem mem_rootSpan_TVBC_iff {y : ModGL Tag.G2 K} :
    y ∈ rootSpan Tag.G2 K TVBC ↔ ∃ ν β γ : K, y = gX rV ν * gX rB β * gX rC γ := by
  constructor
  · intro hy
    have hinj : Function.Injective ![rV, rB, rC] := by decide
    have hrange : Set.range ![rV, rB, rC] = TVBC := by
      ext α; simp [TVBC]; tauto
    obtain ⟨c, -, hc⟩ :=
      (bijOn_prod_pinnedX K pos_TVBC closed_TVBC ![rV, rB, rC] hinj hrange).surjOn hy
    refine ⟨c 0, c 1, c 2, ?_⟩
    rw [← hc]
    simp [List.ofFn_succ, gX, mul_assoc]
  · rintro ⟨ν, β, γ, rfl⟩
    exact (rootSpan Tag.G2 K TVBC).mul_mem ((rootSpan Tag.G2 K TVBC).mul_mem
      (pinnedX_mem_rootSpan (show rV ∈ TVBC from Or.inl rfl) ν)
      (pinnedX_mem_rootSpan (show rB ∈ TVBC from Or.inr (Or.inl rfl)) β))
      (pinnedX_mem_rootSpan (show rC ∈ TVBC from Or.inr (Or.inr rfl)) γ)

theorem gX_rV_not_mem_TBC {s : K} (hs : s ≠ 0) : gX rV s ∉ rootSpan Tag.G2 K TBC := by
  intro h
  have := mem_of_pinnedX_mem_rootSpan pos_TBC closed_TBC (isRoot_pos_iff.2 (by simp)) hs h
  rcases this with h | h <;> revert h <;> decide

theorem pinnedX_eq_pinnedX_of_ne {α β : Fin Tag.G2.rank → ℤ}
    (hα : IsRoot Tag.G2 α ∧ 0 < height α) (hβ : IsRoot Tag.G2 β ∧ 0 < height β) (hne : α ≠ β)
    {s s' : K} (h : pinnedX Tag.G2 K α s = pinnedX Tag.G2 K β s') : s = 0 ∧ s' = 0 := by
  have hinj : Function.Injective ![α, β] := by
    intro i j hij
    fin_cases i <;> fin_cases j
    · rfl
    · exact absurd hij hne
    · exact absurd hij.symm hne
    · rfl
  have hpos : ∀ i, IsRoot Tag.G2 (![α, β] i) ∧ 0 < height (![α, β] i) := by
    intro i
    fin_cases i
    · exact hα
    · exact hβ
  have key := (positive_root_product_injectivity Tag.G2 K ![α, β] hinj hpos).2
  have := @key ![s, 0] ![0, s'] (by
    simp only [List.ofFn_succ, List.ofFn_zero]
    simp [pinnedX_zero, h])
  exact ⟨by simpa using congrFun this 0, by simpa using (congrFun this 1).symm⟩

end NormalForms

end CFSG.Quasithin.H13.F431.G2.Cent
