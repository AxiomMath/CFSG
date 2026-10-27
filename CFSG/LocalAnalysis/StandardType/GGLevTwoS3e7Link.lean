module

public import CFSG.LocalAnalysis.StandardType.GGLevTwoS3e7LinkCheck
public import CFSG.LocalAnalysis.StandardType.GGLevTwoS3bBridge

public section

namespace CFSG.StandardType.LevTwo

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
open CFSG.HardMathSupport.Timmesfeld.CrossChar
open CFSG.LocalAnalysis.GLTheoremB.MovingAround.InputsL33d
open CFSG.LieType.RootSystem
open scoped Matrix

theorem levTwoS3e7_roots_eq : levTwoS3e7_roots = Tag.artifactRoots Tag.E7 := rfl

theorem levTwoS3e7_theta_eq_kacE7 :
    levTwoS3e7_theta = List.ofFn kacE7.θ := rfl

theorem levTwoS3e7_isRoot_iff_mem
    {v : Fin (Tag.rank Tag.E7) → ℤ} :
    IsRoot Tag.E7 v ↔ List.ofFn v ∈ levTwoS3e7_roots := by
  rw [levTwoS3e7_roots_eq]
  exact isRoot_iff_mem_artifactRoots

theorem levTwoS3e7_theta_getD (j : Fin (Tag.rank Tag.E7)) :
    kacE7.θ j = levTwoS3e7_theta.getD j.val 0 := by
  rw [levTwoS3e7_theta_eq_kacE7]
  simp [List.getElem_ofFn]

theorem levTwoS3e7_fin2B_eq (m : ℕ) (β : Fin (Tag.rank Tag.E7) → ℤ) :
    levTwoS3e7_fin2B m β = true ↔ levTwoS3e7_fin2 m β := by
  rw [levTwoS3e7_fin2B, decide_eq_true_eq]

theorem levTwoS3e7_fin2D_iff_fin2
    (D : Finset (Option (Fin (Tag.rank Tag.E7)))) (β : Fin (Tag.rank Tag.E7) → ℤ) :
    (∃ e : Fin 2, ∃ s : Fin 2,
      (e.val = 0 ∨ (none : Option (Fin (Tag.rank Tag.E7))) ∈ D) ∧
      (∀ j : Fin (Tag.rank Tag.E7), 0 ≤ (if s.val = 0 then (1 : ℤ) else -1) * β j +
        (e.val : ℤ) * kacE7.θ j) ∧
      (∀ j : Fin (Tag.rank Tag.E7), (if s.val = 0 then (1 : ℤ) else -1) * β j +
        (e.val : ℤ) * kacE7.θ j ≠ 0 → (some j : Option (Fin (Tag.rank Tag.E7))) ∈ D))
    ↔ levTwoS3e7_fin2 (levTwoS3e7_maskOf D) β := by
  simp only [levTwoS3e7_fin2, levTwoS3e7_maskOf_testBit_none, levTwoS3e7_maskOf_testBit_some,
    levTwoS3e7_theta_getD]

theorem levTwoS3e7_rootsOf_iff_inPat
    (D : Finset (Option (Fin (Tag.rank Tag.E7)))) (hD : D ≠ Finset.univ)
    {β : Fin (Tag.rank Tag.E7) → ℤ} (hβ : IsRoot Tag.E7 β) :
    β ∈ kacE7.rootsOf (D : Set (Option (Fin (Tag.rank Tag.E7)))) ↔
      levTwoS3e7_inPat (levTwoS3e7_maskOf D) (List.ofFn β) = true := by
  rw [levTwoS3b_mem_rootsOf_iff_fin kacE7 facts_E7 D hD hβ, levTwoS3e7_fin2D_iff_fin2]
  have hmem : List.ofFn β ∈ levTwoS3e7_roots := (levTwoS3e7_isRoot_iff_mem).mp hβ
  have h := levTwoS3e7_inPat_eq_fin2B (levTwoS3e7_maskOf_lt D) hmem
  rw [levTwoS3e7_vec_ofFn (Tag.rank Tag.E7) β] at h
  rw [h, levTwoS3e7_fin2B_eq]

@[expose] def levTwoS3e7_patStep (m : ℕ) (acc : ℕ) (i : ℕ) : ℕ :=
  if levTwoS3e7_inPat m (levTwoS3e7_roots.getD i []) then acc ||| (1 <<< i) else acc

theorem levTwoS3e7_patStep_testBit (m acc i j : ℕ) :
    (levTwoS3e7_patStep m acc i).testBit j = true ↔
      acc.testBit j = true ∨
        (i = j ∧ levTwoS3e7_inPat m (levTwoS3e7_roots.getD i []) = true) := by
  unfold levTwoS3e7_patStep
  by_cases h : levTwoS3e7_inPat m (levTwoS3e7_roots.getD i [])
  · rw [if_pos h, Nat.testBit_lor, Bool.or_eq_true, levTwoS3b_testBit_one_shiftLeft]
    constructor
    · rintro (hacc | hji)
      · exact Or.inl hacc
      · exact Or.inr ⟨hji.symm, h⟩
    · rintro (hacc | ⟨hij, -⟩)
      · exact Or.inl hacc
      · exact Or.inr hij.symm
  · rw [if_neg h]
    constructor
    · intro hacc; exact Or.inl hacc
    · rintro (hacc | ⟨-, hpat⟩)
      · exact hacc
      · exact absurd hpat h

theorem levTwoS3e7_foldl_testBit (m : ℕ) (l : List ℕ) (acc j : ℕ) :
    (l.foldl (levTwoS3e7_patStep m) acc).testBit j = true ↔
      acc.testBit j = true ∨
        (j ∈ l ∧ levTwoS3e7_inPat m (levTwoS3e7_roots.getD j []) = true) := by
  induction l generalizing acc with
  | nil => simp
  | cons i l ih =>
      rw [List.foldl_cons, ih (levTwoS3e7_patStep m acc i), levTwoS3e7_patStep_testBit]
      constructor
      · rintro ((hacc | ⟨hij, hpat⟩) | ⟨hjl, hpat⟩)
        · exact Or.inl hacc
        · exact Or.inr ⟨List.mem_cons.mpr (Or.inl hij.symm), hij ▸ hpat⟩
        · exact Or.inr ⟨List.mem_cons.mpr (Or.inr hjl), hpat⟩
      · rintro (hacc | ⟨hjl, hpat⟩)
        · exact Or.inl (Or.inl hacc)
        · rcases List.mem_cons.mp hjl with hji | hjl
          · exact Or.inl (Or.inr ⟨hji.symm, hji ▸ hpat⟩)
          · exact Or.inr ⟨hjl, hpat⟩

theorem levTwoS3e7_patMask_eq (m : ℕ) :
    levTwoS3e7_patMask m = (List.range 126).foldl (levTwoS3e7_patStep m) 0 := rfl

theorem levTwoS3e7_patMask_testBit (m i : ℕ) :
    (levTwoS3e7_patMask m).testBit i = true ↔
      i < 126 ∧ levTwoS3e7_inPat m (levTwoS3e7_roots.getD i []) = true := by
  rw [levTwoS3e7_patMask_eq, levTwoS3e7_foldl_testBit]
  simp [List.mem_range]

theorem levTwoS3e7_isRoot_getD (i : ℕ) (hi : i < 126) :
    IsRoot Tag.E7 (levTwoS3e7_vec (Tag.rank Tag.E7) (levTwoS3e7_roots.getD i [])) := by
  refine (levTwoS3e7_isRoot_iff_mem).mpr ?_
  rw [levTwoS3e7_ofFn_vec (Tag.rank Tag.E7) (levTwoS3e7_roots_getD_length hi)]
  rw [List.getD_eq_getElem _ _ (by rw [levTwoS3e7_roots_length]; exact hi)]
  exact List.getElem_mem (by rw [levTwoS3e7_roots_length]; exact hi)

theorem levTwoS3e7_mem_patSet {m : ℕ}
    {β : Fin (Tag.rank Tag.E7) → ℤ} :
    β ∈ levTwoS3e7_patSet m ↔
      IsRoot Tag.E7 β ∧ levTwoS3e7_inPat m (List.ofFn β) = true := by
  constructor
  · rintro ⟨i, hi, hvec, hbit⟩
    have hbit' := (levTwoS3e7_patMask_testBit m i).mp hbit
    refine ⟨?_, ?_⟩
    · rw [← hvec]
      exact levTwoS3e7_isRoot_getD i hi
    · rw [← hvec]
      rw [levTwoS3e7_ofFn_vec (Tag.rank Tag.E7) (levTwoS3e7_roots_getD_length hi)]
      exact hbit'.2
  · rintro ⟨hroot, hinpat⟩
    have hmem : List.ofFn β ∈ levTwoS3e7_roots := (levTwoS3e7_isRoot_iff_mem).mp hroot
    obtain ⟨i, hi, hri⟩ := List.getElem_of_mem hmem
    have hi126 : i < 126 := by rw [levTwoS3e7_roots_length] at hi; exact hi
    refine ⟨i, hi126, ?_, ?_⟩
    · rw [List.getD_eq_getElem _ _ (by rw [levTwoS3e7_roots_length]; exact hi), hri,
        levTwoS3e7_vec_ofFn]
    · rw [levTwoS3e7_patMask_testBit]
      refine ⟨hi126, ?_⟩
      rw [List.getD_eq_getElem _ _ (by rw [levTwoS3e7_roots_length]; exact hi), hri]
      exact hinpat

theorem levTwoS3e7_partOf_eq
    (D : Finset (Option (Fin (Tag.rank Tag.E7)))) (hD : D ≠ Finset.univ) :
    partOf kacE7 (D : Set (Option (Fin (Tag.rank Tag.E7)))) 2 =
      levTwoS3e7_patSet (levTwoS3e7_maskOf D) := by
  ext β
  constructor
  · rintro ⟨hroot, _⟩
    have hβ : IsRoot Tag.E7 β := hroot.1
    rw [levTwoS3e7_mem_patSet]
    exact ⟨hβ, (levTwoS3e7_rootsOf_iff_inPat D hD hβ).mp hroot⟩
  · intro hβ
    rw [levTwoS3e7_mem_patSet] at hβ
    obtain ⟨hroot, hinpat⟩ := hβ
    exact ⟨(levTwoS3e7_rootsOf_iff_inPat D hD hroot).mpr hinpat,
      iform_self_eq_two_of_simplyLaced' (Or.inr (Or.inr (Or.inl rfl))) hroot⟩

theorem levTwoS3e7_partOf_eq_empty
    (D : Finset (Option (Fin (Tag.rank Tag.E7)))) {l : ℤ} (hl : l ≠ 2) :
    partOf kacE7 (D : Set (Option (Fin (Tag.rank Tag.E7)))) l = ∅ := by
  ext β
  simp only [Set.mem_empty_iff_false, iff_false]
  rintro ⟨hroot, hnorm⟩
  obtain ⟨hβ, -⟩ := hroot
  exact hl (by rw [← hnorm]; exact iform_self_eq_two_of_simplyLaced' (Or.inr (Or.inr (Or.inl rfl))) hβ)

theorem levTwoS3e7_mask_cases
    (D : Finset (Option (Fin (Tag.rank Tag.E7)))) (l : ℤ) (hD : D ≠ Finset.univ)
    (hirr : ∀ α ∈ partOf kacE7 (D : Set (Option (Fin (Tag.rank Tag.E7)))) l,
      ∀ β ∈ partOf kacE7 (D : Set (Option (Fin (Tag.rank Tag.E7)))) l,
      Relation.ReflTransGen
        (fun a b => b ∈ partOf kacE7 (D : Set (Option (Fin (Tag.rank Tag.E7)))) l ∧
          iform a b ≠ 0) α β)
    (hrank : ∃ s : Finset (Fin (Tag.rank Tag.E7) → ℤ),
      (s : Set (Fin (Tag.rank Tag.E7) → ℤ)) ⊆
        partOf kacE7 (D : Set (Option (Fin (Tag.rank Tag.E7)))) l ∧
      LinearIndependent ℚ (fun v : s => (fun i => ((v : Fin (Tag.rank Tag.E7) → ℤ) i : ℚ))) ∧
      ExcRankOK Tag.E7 s.card) :
    levTwoS3e7_maskOf D ∈ levTwoS3e7_survivors ∧ l = 2 ∧
      partOf kacE7 (D : Set (Option (Fin (Tag.rank Tag.E7)))) 2 =
        levTwoS3e7_patSet (levTwoS3e7_maskOf D) := by
  obtain ⟨s, hs, hli, hrank⟩ := hrank
  have hli' : LinearIndependent ℚ (fun v : s => toRat (v : Fin (Tag.rank Tag.E7) → ℤ)) := by
    have hfun : (fun v : s => toRat (v : Fin (Tag.rank Tag.E7) → ℤ)) =
        (fun v : s => fun i => ((v : Fin (Tag.rank Tag.E7) → ℤ) i : ℚ)) := by
      funext v i
      rw [toRat_apply]
    rw [hfun]
    exact hli
  have hle : s.card ≤ D.card :=
    levTwoS3b_card_le_of_linearIndependent kacE7 D l s hs hli'
  have h6D : 6 ≤ D.card := by
    have h6s : 6 ≤ s.card := by
      rcases (levTwoS3b_excRankOK_le_card hrank (le_refl s.card)).2.2 with h | h
      · have h7 : Tag.E7.rank = 7 := rfl
        omega
      · exact absurd h (by decide)
    omega
  have h6 : 6 ≤ levTwoS3e7_maskPop (levTwoS3e7_maskOf D) := by
    rw [levTwoS3e7_card_eq_pop]
    exact h6D
  have hl2 : l = 2 := by
    by_contra hl
    have hne : (partOf kacE7 (D : Set (Option (Fin (Tag.rank Tag.E7)))) l).Nonempty := by
      have hpos : 0 < s.card := by have := hrank.1; omega
      obtain ⟨x, hx⟩ := Finset.card_pos.mp hpos
      exact ⟨x, hs hx⟩
    rw [levTwoS3e7_partOf_eq_empty D hl] at hne
    exact hne.ne_empty rfl
  have hirr' : levTwoS3e7_irred (levTwoS3e7_maskOf D) := by
    unfold levTwoS3e7_irred
    rw [← levTwoS3e7_partOf_eq D hD, ← hl2]
    exact hirr
  exact ⟨levTwoS3e7_irred_mask_cases (levTwoS3e7_maskOf D)
      (levTwoS3e7_maskOf_lt_of_ne_univ D hD) h6 hirr',
    hl2, levTwoS3e7_partOf_eq D hD⟩

end CFSG.StandardType.LevTwo
