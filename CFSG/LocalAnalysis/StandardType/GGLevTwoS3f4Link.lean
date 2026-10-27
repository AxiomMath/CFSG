module

public import CFSG.LocalAnalysis.StandardType.GGLevTwoS3bLink
public import CFSG.LocalAnalysis.StandardType.GGLevTwoS3f4Filter
public import CFSG.Mathlib.Decide.Bounded

public section

namespace CFSG.StandardType.LevTwo

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
open CFSG.HardMathSupport.Timmesfeld.CrossChar
open CFSG.LieType.RootSystem
open scoped Matrix

@[expose] def levTwoS3f4_nodeIdx : Option (Fin (Tag.rank Tag.F4)) → ℕ
  | none => 0
  | some j => j.val + 1

@[expose] def levTwoS3f4_maskOf (D : Finset (Option (Fin (Tag.rank Tag.F4)))) : ℕ :=
  ∑ x ∈ D, 2 ^ levTwoS3f4_nodeIdx x

@[expose] def levTwoS3f4_thetaVec : Fin (Tag.rank Tag.F4) → ℤ := ![2, 3, 4, 2]

theorem levTwoS3f4_theta_eq :
    kacF4.θ = levTwoS3f4_thetaVec := rfl

theorem levTwoS3f4_ofFn_getD (β : Fin (Tag.rank Tag.F4) → ℤ) (j : Fin (Tag.rank Tag.F4)) :
    (List.ofFn β).getD j.val 0 = β j :=
  congrFun (levTwoS3f4_vec_ofFn (Tag.rank Tag.F4) β) j

open scoped CFSG.Decide.Bounded in
theorem levTwoS3f4_fin2_iff_inPat :
    ∀ D : Finset (Option (Fin (Tag.rank Tag.F4))), D ≠ Finset.univ →
      ∀ l ∈ Tag.F4.artifactRoots,
        (∃ e : Fin 2, ∃ s : Fin 2,
          (e.val = 0 ∨ (none : Option (Fin (Tag.rank Tag.F4))) ∈ D) ∧
          (∀ j, 0 ≤ (if s.val = 0 then (1 : ℤ) else -1) * l.getD j.val 0 +
            (e.val : ℤ) * levTwoS3f4_thetaVec j) ∧
          (∀ j, (if s.val = 0 then (1 : ℤ) else -1) * l.getD j.val 0 +
            (e.val : ℤ) * levTwoS3f4_thetaVec j ≠ 0 →
              (some j : Option (Fin (Tag.rank Tag.F4))) ∈ D)) ↔
        levTwoS3f4_inPat (levTwoS3f4_maskOf D) l = true := by
  decide +kernel

theorem levTwoS3f4_rootsOf_iff_inPat
    (D : Finset (Option (Fin (Tag.rank Tag.F4))))
    (hD : D ≠ Finset.univ) {β : Fin (Tag.rank Tag.F4) → ℤ} (hβ : IsRoot Tag.F4 β) :
    β ∈ kacF4.rootsOf (D : Set (Option (Fin (Tag.rank Tag.F4)))) ↔
      levTwoS3f4_inPat (levTwoS3f4_maskOf D) (List.ofFn β) = true := by
  rw [levTwoS3b_mem_rootsOf_iff_fin kacF4 facts_F4 D hD hβ]
  rw [levTwoS3f4_theta_eq]
  have hmem : List.ofFn β ∈ Tag.F4.artifactRoots := (isRoot_iff_mem_artifactRoots).mp hβ
  have hbr := levTwoS3f4_fin2_iff_inPat D hD (List.ofFn β) hmem
  simpa only [levTwoS3f4_ofFn_getD] using hbr

open scoped CFSG.Decide.Bounded in
theorem levTwoS3f4_mem_patSet_iff :
    ∀ D : Finset (Option (Fin (Tag.rank Tag.F4))), ∀ l ∈ [2, 4],
      ∀ v ∈ Tag.F4.artifactRoots,
        levTwoS3f4_vec (Tag.rank Tag.F4) v ∈ levTwoS3f4_patSet (levTwoS3f4_maskOf D) l ↔
          levTwoS3f4_inPat (levTwoS3f4_maskOf D) v = true ∧ levTwoS3f4_ipf v v = (l : ℤ) := by
  decide +kernel

theorem levTwoS3f4_isRoot_of_mem_patSet
    {m l : ℕ} {β : Fin (Tag.rank Tag.F4) → ℤ}
    (h : β ∈ levTwoS3f4_patSet m l) : IsRoot Tag.F4 β := by
  rw [levTwoS3f4_patSet] at h
  obtain ⟨i, hi, hβi⟩ := List.mem_map.mp (List.mem_toFinset.mp h)
  rw [List.mem_filter] at hi
  have hi48 : i < 48 := List.mem_range.mp hi.1
  have hlen : levTwoS3f4_roots.length = 48 := by decide
  have hilt : i < levTwoS3f4_roots.length := by rw [hlen]; exact hi48
  have hget : levTwoS3f4_roots.getD i [] = levTwoS3f4_roots[i] :=
    List.getD_eq_getElem levTwoS3f4_roots [] hilt
  rw [hget] at hβi
  have hmem : levTwoS3f4_roots[i] ∈ levTwoS3f4_roots :=
    List.mem_iff_getElem.mpr ⟨i, hilt, rfl⟩
  rw [← hβi, isRoot_iff_mem_artifactRoots,
    levTwoS3f4_ofFn_vec (Tag.rank Tag.F4) (length_of_mem_artifactRoots hmem)]
  exact hmem

open scoped CFSG.Decide.Bounded in
theorem levTwoS3f4_ipf_self_cases (v : List ℤ) (hv : v ∈ Tag.F4.artifactRoots) :
    levTwoS3f4_ipf v v = 2 ∨ levTwoS3f4_ipf v v = 4 := by
  revert hv
  revert v
  decide +kernel

theorem levTwoS3f4_iform_self_cases
    {β : Fin (Tag.rank Tag.F4) → ℤ} (hβ : IsRoot Tag.F4 β) :
    iform β β = 2 ∨ iform β β = 4 := by
  have hmem : List.ofFn β ∈ Tag.F4.artifactRoots := (isRoot_iff_mem_artifactRoots).mp hβ
  have h := levTwoS3f4_ipf_self_cases (List.ofFn β) hmem
  rwa [levTwoS3f4_ipf_eq_iform_of_length (by simp) (by simp), levTwoS3f4_vec_ofFn] at h

theorem levTwoS3f4_partOf_eq
    (D : Finset (Option (Fin (Tag.rank Tag.F4))))
    (hD : D ≠ Finset.univ) (l : ℕ) (hl : l = 2 ∨ l = 4) :
    partOf kacF4 (D : Set (Option (Fin (Tag.rank Tag.F4)))) (l : ℤ) =
      ↑(levTwoS3f4_patSet (levTwoS3f4_maskOf D) l) := by
  ext β
  rw [partOf, Set.mem_setOf_eq]
  constructor
  · rintro ⟨hroot, hnorm⟩
    have hβ : IsRoot Tag.F4 β := hroot.1
    rw [levTwoS3f4_rootsOf_iff_inPat D hD hβ] at hroot
    have hmem : List.ofFn β ∈ Tag.F4.artifactRoots := (isRoot_iff_mem_artifactRoots).mp hβ
    rw [← levTwoS3f4_vec_ofFn (Tag.rank Tag.F4) β, Finset.mem_coe,
      levTwoS3f4_mem_patSet_iff D l (by simpa using hl) (List.ofFn β) hmem]
    refine ⟨hroot, ?_⟩
    rw [levTwoS3f4_ipf_eq_iform_of_length (by simp) (by simp), levTwoS3f4_vec_ofFn]
    exact hnorm
  · intro h
    have hβ : IsRoot Tag.F4 β := levTwoS3f4_isRoot_of_mem_patSet h
    have hmem : List.ofFn β ∈ Tag.F4.artifactRoots := (isRoot_iff_mem_artifactRoots).mp hβ
    have h' : levTwoS3f4_vec (Tag.rank Tag.F4) (List.ofFn β) ∈
        levTwoS3f4_patSet (levTwoS3f4_maskOf D) l := by
      rw [levTwoS3f4_vec_ofFn]
      exact Finset.mem_coe.mp h
    rw [levTwoS3f4_mem_patSet_iff D l (by simpa using hl) (List.ofFn β) hmem] at h'
    obtain ⟨hin, hipf⟩ := h'
    refine ⟨?_, ?_⟩
    · rw [levTwoS3f4_rootsOf_iff_inPat D hD hβ]
      exact hin
    · rw [← levTwoS3f4_vec_ofFn (Tag.rank Tag.F4) β,
        ← levTwoS3f4_ipf_eq_iform_of_length (by simp) (by simp)]
      exact hipf

open scoped CFSG.Decide.Bounded in
theorem levTwoS3f4_popCount_maskOf (D : Finset (Option (Fin (Tag.rank Tag.F4)))) :
    levTwoS3f4_popCount (levTwoS3f4_maskOf D) = D.card := by
  revert D
  decide +kernel

open scoped CFSG.Decide.Bounded in
theorem levTwoS3f4_maskOf_lt_31 (D : Finset (Option (Fin (Tag.rank Tag.F4))))
    (hD : D ≠ Finset.univ) : levTwoS3f4_maskOf D < 31 := by
  revert hD
  revert D
  decide +kernel

@[expose] def levTwoS3f4_irredSet (S : Set (Fin (Tag.rank Tag.F4) → ℤ)) : Prop :=
  ∀ α ∈ S, ∀ β ∈ S, Relation.ReflTransGen (fun a b => b ∈ S ∧ iform a b ≠ 0) α β

theorem levTwoS3f4_irreducible_eq_irredSet (m l : ℕ) :
    levTwoS3f4_irreducible m l ↔ levTwoS3f4_irredSet ↑(levTwoS3f4_patSet m l) :=
  Iff.rfl

theorem levTwoS3f4_mask_cases
    (D : Finset (Option (Fin (Tag.rank Tag.F4)))) (l : ℤ)
    (hD : D ≠ Finset.univ)
    (hirr : levTwoS3f4_irredSet (partOf kacF4 (D : Set (Option (Fin (Tag.rank Tag.F4)))) l))
    (hind : ∃ s : Finset (Fin (Tag.rank Tag.F4) → ℤ),
      (s : Set (Fin (Tag.rank Tag.F4) → ℤ)) ⊆
        partOf kacF4 (D : Set (Option (Fin (Tag.rank Tag.F4)))) l ∧
      LinearIndependent ℚ (fun x : s => toRat (x : Fin (Tag.rank Tag.F4) → ℤ)) ∧
      ExcRankOK Tag.F4 s.card) :
    (levTwoS3f4_maskOf D, l.toNat) ∈ levTwoS3f4_survivors ∧
      partOf kacF4 (D : Set (Option (Fin (Tag.rank Tag.F4)))) l =
        ↑(levTwoS3f4_patSet (levTwoS3f4_maskOf D) l.toNat) := by
  obtain ⟨s, hs, hli, hrank⟩ := hind
  have h3 : 3 ≤ s.card := hrank.1
  have hsne : s.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨β, hβs⟩ := hsne
  have hβpart := hs hβs
  have hβroot : IsRoot Tag.F4 β := hβpart.1.1
  have hnorm : iform β β = l := hβpart.2
  have hl : l = 2 ∨ l = 4 := by
    rcases levTwoS3f4_iform_self_cases hβroot with h | h <;> omega
  have hlt : l.toNat = 2 ∨ l.toNat = 4 := by omega
  have hlz : (l.toNat : ℤ) = l := by omega
  have hpart := levTwoS3f4_partOf_eq D hD l.toNat hlt
  rw [hlz] at hpart
  have hirr' : levTwoS3f4_irreducible (levTwoS3f4_maskOf D) l.toNat := by
    rw [levTwoS3f4_irreducible_eq_irredSet]
    rwa [hpart] at hirr
  have hfun : (fun x : s => (fun i => (((x : Fin (Tag.rank Tag.F4) → ℤ) i : ℤ) : ℚ))) =
      (fun x : s => toRat (x : Fin (Tag.rank Tag.F4) → ℤ)) := by
    funext x i
    rw [toRat_apply]
  have hli' : LinearIndependent ℚ
      (fun x : s => (fun i => (((x : Fin (Tag.rank Tag.F4) → ℤ) i : ℤ) : ℚ))) := by
    rw [hfun]
    exact hli
  have h3ind : levTwoS3f4_hasThreeInd (levTwoS3f4_maskOf D) l.toNat := by
    refine ⟨s, ?_, hli', h3⟩
    rw [← hpart]
    exact hs
  have hcard : s.card ≤ D.card :=
    levTwoS3b_card_le_of_linearIndependent kacF4 D l s hs hli
  have hpc : 3 ≤ levTwoS3f4_popCount (levTwoS3f4_maskOf D) := by
    rw [levTwoS3f4_popCount_maskOf]
    exact (levTwoS3b_excRankOK_le_card hrank hcard).1
  have hmem : l.toNat ∈ [2, 4] := by
    rcases hlt with h | h <;> simp [h]
  have hsurv :=
    levTwoS3f4_irred_mask_cases (levTwoS3f4_maskOf D) (levTwoS3f4_maskOf_lt_31 D hD)
      l.toNat hmem hpc hirr' h3ind
  exact ⟨hsurv, hpart⟩

end CFSG.StandardType.LevTwo
