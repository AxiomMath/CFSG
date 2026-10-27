module

public import CFSG.Quasithin.Recognition.L34AmalgamGen

public section

namespace CFSG.Quasithin.L34Amalgam

open MulAction CFSG.ComponentClassification.WittDesign CFSG.Quasithin.Asc94 CFSG.CosetTable

@[expose] noncomputable def gen₁ (j : Fin 5) : ↥m22TwoStab :=
  if h : j = 4 then 1 else ⟨gen j, gen_mem_two j h⟩

@[expose] noncomputable def gen₂ (j : Fin 5) : ↥m22PtHexStab :=
  if h : j = 3 then 1 else ⟨gen j, gen_mem_ptHex j h⟩

theorem coe_gen₁
    {j : Fin 5} (hj : j ≠ 4) : (gen₁ j : M22) = gen j := by
  rw [gen₁, dite_eq_right hj]

theorem coe_gen₂
    {j : Fin 5} (hj : j ≠ 3) : (gen₂ j : M22) = gen j := by
  rw [gen₂, dite_eq_right hj]

@[expose] def genK (j : Fin 5) : ↥(stabilizer M22 (0 : Fin 22)) :=
  ⟨gen j, by
    by_cases hj : j = 4
    · rw [hj, gen_four]
      exact (Subgroup.mem_inf.mp bT2_mem_ptHex).1
    · exact (Subgroup.mem_inf.mp (gen_mem_two j hj)).1⟩

theorem letters_ne_four {s : String} (hs : s ∈ rels1) : ∀ x ∈ word s, x.1 ≠ 4 :=
  letters_facts.1 s hs

theorem letters_ne_three {s : String} (hs : s ∈ rels2) : ∀ x ∈ word s, x.1 ≠ 3 :=
  letters_facts.2.1 s hs

theorem coe_evalW_gen₁
    {w : List (Fin 5 × Bool)} (hw : ∀ x ∈ w, x.1 ≠ 4) :
    ((evalW gen₁ w : ↥m22TwoStab) : M22) = evalW gen w :=
  (evalW_map m22TwoStab.subtype gen₁ gen w fun x hx => (coe_gen₁ (hw x hx)).symm).symm

theorem coe_evalW_gen₂
    {w : List (Fin 5 × Bool)} (hw : ∀ x ∈ w, x.1 ≠ 3) :
    ((evalW gen₂ w : ↥m22PtHexStab) : M22) = evalW gen w :=
  (evalW_map m22PtHexStab.subtype gen₂ gen w fun x hx => (coe_gen₂ (hw x hx)).symm).symm

theorem closure_gen₁
    : Subgroup.closure (gen₁ '' {0, 1, 2, 3}) = ⊤ := by
  apply Subgroup.map_injective m22TwoStab.subtype_injective
  rw [MonoidHom.map_closure, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  refine Eq.trans ?_ closure_gen_P1
  congr 1
  ext g
  simp only [Set.mem_image, Subgroup.coe_subtype]
  constructor
  · rintro ⟨_, ⟨j, hj, rfl⟩, rfl⟩
    exact ⟨j, hj, (coe_gen₁ (by rintro rfl; simp at hj)).symm⟩
  · rintro ⟨j, hj, rfl⟩
    exact ⟨_, ⟨j, hj, rfl⟩, coe_gen₁ (by rintro rfl; simp at hj)⟩

theorem closure_gen₂
    : Subgroup.closure (gen₂ '' {0, 1, 2, 4}) = ⊤ := by
  apply Subgroup.map_injective m22PtHexStab.subtype_injective
  rw [MonoidHom.map_closure, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  refine Eq.trans ?_ closure_gen_P2
  congr 1
  ext g
  simp only [Set.mem_image, Subgroup.coe_subtype]
  constructor
  · rintro ⟨_, ⟨j, hj, rfl⟩, rfl⟩
    exact ⟨j, hj, (coe_gen₂ (by rintro rfl; simp at hj)).symm⟩
  · rintro ⟨j, hj, rfl⟩
    exact ⟨_, ⟨j, hj, rfl⟩, coe_gen₂ (by rintro rfl; simp at hj)⟩

section Amalgam

variable {L : Type*} [Group L] {L₁ L₂ : Subgroup L}
  (φ₁ : ↥m22TwoStab ≃* ↥L₁) (φ₂ : ↥m22PtHexStab ≃* ↥L₂)

@[expose] noncomputable def genL (j : Fin 5) : L :=
  if j = 4 then (φ₂ (gen₂ j) : L) else (φ₁ (gen₁ j) : L)

variable {φ₁ φ₂}

variable (hB : ∀ (b : M22) (h₁ : b ∈ m22TwoStab) (h₂ : b ∈ m22PtHexStab),
  (φ₁ ⟨b, h₁⟩ : L) = φ₂ ⟨b, h₂⟩)
include hB

omit hB in
theorem genL_eq₁
    {j : Fin 5} (hj : j ≠ 4) : genL φ₁ φ₂ j = φ₁ (gen₁ j) := by
  rw [genL, ite_eq_right hj]

theorem genL_eq₂
    {j : Fin 5} (hj : j ≠ 3) : genL φ₁ φ₂ j = φ₂ (gen₂ j) := by
  by_cases h4 : j = 4
  · rw [genL, ite_eq_left h4]
  · rw [genL, ite_eq_right h4]
    have e1 : gen₁ j = ⟨gen j, gen_mem_two j h4⟩ := Subtype.ext (coe_gen₁ h4)
    have e2 : gen₂ j = ⟨gen j, gen_mem_ptHex j hj⟩ := Subtype.ext (coe_gen₂ hj)
    rw [e1, e2]
    exact hB _ _ _

theorem evalW_genL_amalRels
    : ∀ w ∈ amalRels, evalW (genL φ₁ φ₂) w = 1 := by
  intro w hw
  obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hw
  rcases List.mem_append.mp hs with hs | hs
  · have hl := letters_ne_four hs
    rw [evalW_map (L₁.subtype.comp φ₁.toMonoidHom) gen₁ (genL φ₁ φ₂) _
      fun x hx => genL_eq₁ (hl x hx)]
    have h1 : evalW gen₁ (word s) = 1 := by
      apply Subtype.ext
      rw [coe_evalW_gen₁ hl, evalW_amalRels _ (List.mem_map_of_mem (List.mem_append_left _ hs))]
      rfl
    rw [h1, map_one]
  · have hl := letters_ne_three hs
    rw [evalW_map (L₂.subtype.comp φ₂.toMonoidHom) gen₂ (genL φ₁ φ₂) _
      fun x hx => genL_eq₂ hB (hl x hx)]
    have h1 : evalW gen₂ (word s) = 1 := by
      apply Subtype.ext
      rw [coe_evalW_gen₂ hl, evalW_amalRels _ (List.mem_map_of_mem (List.mem_append_right _ hs))]
      rfl
    rw [h1, map_one]

omit hB in
theorem rep_mem (i : Fin 12) : rep i ∈ m22PtHexStab := by
  rw [rep, ← coe_evalW_gen₂ (letters_facts.2.2 i)]
  exact (evalW gen₂ _).2

theorem evalW_genL_rep (i : Fin 12) :
    evalW (genL φ₁ φ₂) (word (repStr i)) = φ₂ ⟨rep i, rep_mem i⟩ := by
  have hl := letters_facts.2.2 i
  rw [evalW_map (L₂.subtype.comp φ₂.toMonoidHom) gen₂ (genL φ₁ φ₂) _
    fun x hx => genL_eq₂ hB (hl x hx)]
  have e : evalW gen₂ (word (repStr i)) = ⟨rep i, rep_mem i⟩ :=
    Subtype.ext (coe_evalW_gen₂ hl)
  rw [e]
  rfl

@[expose] noncomputable def homL {ws : List (List (Fin 5 × Bool))}
    (hws : ∀ w ∈ ws, evalW (genL φ₁ φ₂) w = 1) : PG 5 ws →* L :=
  PresentedGroup.toGroup (f := genL φ₁ φ₂) fun r hr => by
    obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hr
    rw [← evalW_eq_lift]
    exact hws w hw

omit hB in
theorem homL_of
    {ws : List (List (Fin 5 × Bool))} (hws : ∀ w ∈ ws, evalW (genL φ₁ φ₂) w = 1)
    (j : Fin 5) : homL hws (PresentedGroup.of j) = genL φ₁ φ₂ j :=
  PresentedGroup.toGroup.of _

end Amalgam

theorem mem_subsetOf_iff (j : Fin 5) : j ∈ subsetOf 5 [0, 1, 2, 3] ↔ j ≠ 4 := by
  fin_cases j <;> decide

theorem index_genSub_le {ws : List (List (Fin 5 × Bool))} {n : ℕ}
    (h : subsetCheck ws [0, 1, 2, 3] 100000 n = true) :
    (genSub {r : FreeGroup (Fin 5) | r ∈ ws.map FreeGroup.mk}
        (subsetOf 5 [0, 1, 2, 3])).FiniteIndex ∧
      (genSub {r : FreeGroup (Fin 5) | r ∈ ws.map FreeGroup.mk}
        (subsetOf 5 [0, 1, 2, 3])).index ≤ n :=
  index_le_presented ws ((subsetOf 5 [0, 1, 2, 3]).map fun x => [(x, true)]) _
    (by
      intro w hw
      simp only [List.mem_map] at hw
      obtain ⟨x, hx, rfl⟩ := hw
      exact Subgroup.subset_closure ⟨x, hx, rfl⟩) h

end CFSG.Quasithin.L34Amalgam
