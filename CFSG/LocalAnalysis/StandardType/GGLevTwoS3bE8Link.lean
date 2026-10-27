module

public import CFSG.LocalAnalysis.StandardType.GGLevTwoS3bE8LinkCheck
public import CFSG.LocalAnalysis.StandardType.GGLevTwoS3bLink
public import CFSG.LocalAnalysis.StandardType.GGLevTwoS3bSem
public import CFSG.Mathlib.Decide.Bounded

public section

namespace CFSG.StandardType.LevTwo

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
open CFSG.HardMathSupport.Timmesfeld.CrossChar
open CFSG.LieType.RootSystem
open scoped Matrix

theorem levTwoS3b_e8_theta_eq :
    kacE8.θ = levTwoS3b_e8ThetaVec := rfl

theorem levTwoS3b_e8_ofFn_getD (β : Fin (Tag.rank Tag.E8) → ℤ)
    (j : Fin (Tag.rank Tag.E8)) :
    (List.ofFn β).getD j.val 0 = β j :=
  congrFun (levTwoS3b_vec_ofFn (Tag.rank Tag.E8) β) j

theorem levTwoS3b_e8_roots_length240 : levTwoS3b_roots.length = 240 := by
  decide +kernel

theorem levTwoS3b_e8_roots_length {i : ℕ} (hi : i < 240) :
    (levTwoS3b_roots.getD i []).length = 8 := by
  have hlen : levTwoS3b_roots.length = 240 := levTwoS3b_e8_roots_length240
  have hi' : i < levTwoS3b_roots.length := by rw [hlen]; exact hi
  have hmem : levTwoS3b_roots.getD i [] ∈ Tag.E8.artifactRoots := by
    rw [List.getD_eq_getElem levTwoS3b_roots [] hi']
    exact List.getElem_mem hi'
  have h := length_of_mem_artifactRoots (τ := Tag.E8) hmem
  simpa [levTwoS3b_roots, Tag.rank] using h

theorem levTwoS3b_e8_vec_injOn {v w : List ℤ} (hv : v.length = 8) (hw : w.length = 8)
    (h : levTwoS3b_vec (Tag.rank Tag.E8) v = levTwoS3b_vec (Tag.rank Tag.E8) w) : v = w := by
  have hv' : List.ofFn (levTwoS3b_vec (Tag.rank Tag.E8) v) = v :=
    levTwoS3b_ofFn_vec (Tag.rank Tag.E8) hv
  have hw' : List.ofFn (levTwoS3b_vec (Tag.rank Tag.E8) w) = w :=
    levTwoS3b_ofFn_vec (Tag.rank Tag.E8) hw
  rw [← hv', ← hw', h]

open scoped CFSG.Decide.Bounded in
theorem levTwoS3b_e8_maskOf_lt_512 (D : Finset (Option (Fin (Tag.rank Tag.E8)))) :
    levTwoS3b_e8_maskOf D < 512 := by
  revert D
  decide +kernel

open scoped CFSG.Decide.Bounded in
theorem levTwoS3b_e8_maskOf_lt_511 (D : Finset (Option (Fin (Tag.rank Tag.E8))))
    (hD : D ≠ Finset.univ) : levTwoS3b_e8_maskOf D < 511 := by
  revert hD
  revert D
  decide +kernel

theorem levTwoS3b_e8_fin2_iff_inPat :
    ∀ D : Finset (Option (Fin (Tag.rank Tag.E8))), D ≠ Finset.univ →
      ∀ l ∈ Tag.E8.artifactRoots,
        (∃ e : Fin 2, ∃ s : Fin 2,
          (e.val = 0 ∨ (none : Option (Fin (Tag.rank Tag.E8))) ∈ D) ∧
          (∀ j, 0 ≤ (if s.val = 0 then (1 : ℤ) else -1) * l.getD j.val 0 +
            (e.val : ℤ) * levTwoS3b_e8ThetaVec j) ∧
          (∀ j, (if s.val = 0 then (1 : ℤ) else -1) * l.getD j.val 0 +
            (e.val : ℤ) * levTwoS3b_e8ThetaVec j ≠ 0 →
              (some j : Option (Fin (Tag.rank Tag.E8))) ∈ D)) ↔
        levTwoS3b_inPat (levTwoS3b_e8_maskOf D) l = true := by
  intro D hD l hl
  exact (levTwoS3b_e8_linkBlock_all
      ⟨levTwoS3b_e8_maskOf D / 64, by
        have := levTwoS3b_e8_maskOf_lt_512 D
        omega⟩)
    D (Finset.mem_filter.mpr ⟨Finset.mem_univ D, rfl⟩) hD l hl

theorem levTwoS3b_e8_rootsOf_iff_inPat
    (D : Finset (Option (Fin (Tag.rank Tag.E8)))) (hD : D ≠ Finset.univ)
    {β : Fin (Tag.rank Tag.E8) → ℤ} (hβ : IsRoot Tag.E8 β) :
    β ∈ kacE8.rootsOf (D : Set (Option (Fin (Tag.rank Tag.E8)))) ↔
      levTwoS3b_inPat (levTwoS3b_e8_maskOf D) (List.ofFn β) = true := by
  rw [levTwoS3b_mem_rootsOf_iff_fin kacE8 facts_E8 D hD hβ]
  rw [levTwoS3b_e8_theta_eq]
  have hmem : List.ofFn β ∈ Tag.E8.artifactRoots := (isRoot_iff_mem_artifactRoots).mp hβ
  have hbr := levTwoS3b_e8_fin2_iff_inPat D hD (List.ofFn β) hmem
  simpa only [levTwoS3b_e8_ofFn_getD] using hbr

@[expose] def levTwoS3b_e8_patSet (m : ℕ) : Set (Fin (Tag.rank Tag.E8) → ℤ) :=
  {β | ∃ i < 240, levTwoS3b_vec (Tag.rank Tag.E8) (levTwoS3b_roots.getD i []) = β ∧
    levTwoS3b_inPat m (levTwoS3b_roots.getD i []) = true}

theorem levTwoS3b_e8_mem_patSet_iff {m : ℕ} {β : Fin (Tag.rank Tag.E8) → ℤ}
    (hmem : List.ofFn β ∈ levTwoS3b_roots) :
    β ∈ levTwoS3b_e8_patSet m ↔ levTwoS3b_inPat m (List.ofFn β) = true := by
  constructor
  · rintro ⟨i, hi, hveq, hpat⟩
    rw [← hveq, levTwoS3b_ofFn_vec (Tag.rank Tag.E8) (levTwoS3b_e8_roots_length hi), hpat]
  · intro h
    obtain ⟨i, hi, hget⟩ := List.mem_iff_getElem.mp hmem
    have hi' : i < 240 := by
      rw [levTwoS3b_e8_roots_length240] at hi
      exact hi
    refine ⟨i, hi', ?_, ?_⟩
    · rw [List.getD_eq_getElem levTwoS3b_roots [] hi, hget]
      exact levTwoS3b_vec_ofFn (Tag.rank Tag.E8) β
    · rw [List.getD_eq_getElem levTwoS3b_roots [] hi, hget]
      exact h

theorem levTwoS3b_e8_isRoot_of_mem_patSet {m : ℕ}
    {β : Fin (Tag.rank Tag.E8) → ℤ} (h : β ∈ levTwoS3b_e8_patSet m) : IsRoot Tag.E8 β := by
  obtain ⟨i, hi, hveq, -⟩ := h
  rw [← hveq, isRoot_iff_mem_artifactRoots]
  rw [levTwoS3b_ofFn_vec (Tag.rank Tag.E8) (levTwoS3b_e8_roots_length hi)]
  have hmem : levTwoS3b_roots.getD i [] ∈ levTwoS3b_roots := by
    rw [List.getD_eq_getElem levTwoS3b_roots [] (by rw [levTwoS3b_e8_roots_length240]; exact hi)]
    exact List.getElem_mem (by rw [levTwoS3b_e8_roots_length240]; exact hi)
  simpa [levTwoS3b_roots] using hmem

open scoped CFSG.Decide.Bounded in
theorem levTwoS3b_e8_ipf_self (v : List ℤ) (hv : v ∈ Tag.E8.artifactRoots) :
    levTwoS3b_ipf v v = 2 := by
  revert hv
  revert v
  decide +kernel

theorem levTwoS3b_e8_iform_self
    {β : Fin (Tag.rank Tag.E8) → ℤ} (hβ : IsRoot Tag.E8 β) : iform β β = 2 := by
  have hmem : List.ofFn β ∈ Tag.E8.artifactRoots := (isRoot_iff_mem_artifactRoots).mp hβ
  have h := levTwoS3b_e8_ipf_self (List.ofFn β) hmem
  rwa [levTwoS3b_ipf_eq_iform_of_length (by simp) (by simp), levTwoS3b_vec_ofFn] at h

theorem levTwoS3b_e8_partOf_eq
    (D : Finset (Option (Fin (Tag.rank Tag.E8)))) (hD : D ≠ Finset.univ) :
    partOf kacE8 (D : Set (Option (Fin (Tag.rank Tag.E8)))) 2 =
      levTwoS3b_e8_patSet (levTwoS3b_e8_maskOf D) := by
  ext β
  rw [partOf, Set.mem_setOf_eq]
  constructor
  · rintro ⟨hroot, -⟩
    have hβ : IsRoot Tag.E8 β := hroot.1
    rw [levTwoS3b_e8_rootsOf_iff_inPat D hD hβ] at hroot
    have hmem : List.ofFn β ∈ Tag.E8.artifactRoots := (isRoot_iff_mem_artifactRoots).mp hβ
    rw [levTwoS3b_e8_mem_patSet_iff (by simpa [levTwoS3b_roots] using hmem)]
    exact hroot
  · intro h
    have hβ : IsRoot Tag.E8 β := levTwoS3b_e8_isRoot_of_mem_patSet h
    have hmem : List.ofFn β ∈ Tag.E8.artifactRoots := (isRoot_iff_mem_artifactRoots).mp hβ
    have hpat : levTwoS3b_inPat (levTwoS3b_e8_maskOf D) (List.ofFn β) = true :=
      (levTwoS3b_e8_mem_patSet_iff (by simpa [levTwoS3b_roots] using hmem)).mp h
    refine ⟨?_, levTwoS3b_e8_iform_self hβ⟩
    rw [levTwoS3b_e8_rootsOf_iff_inPat D hD hβ]
    exact hpat

end CFSG.StandardType.LevTwo
