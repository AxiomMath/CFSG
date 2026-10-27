module

public import CFSG.LocalAnalysis.WeakClosure81.SpUCitedParSpBasic
public import CFSG.LocalAnalysis.WeakClosure81.SpUCitedParLattice

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Open CFSG.RankThree.PartOne.KCSpFull CFSG.RankThree.Classical
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher

variable {r : ℕ} {K : Type} [Field K]

private theorem spUCited_borel_eq :
    borelSubgroup r K = flagStabilizer r K (Set.Icc 1 r) := by
  ext g
  simp only [mem_borelSubgroup, mem_flagStabilizer, Set.mem_Icc]
  constructor
  · intro h i hi
    exact h i hi.1 hi.2
  · intro h i hi1 hir
    exact h i ⟨hi1, hir⟩

private theorem spUCited_mem_flagStabilizer_weylRep {I : Set ℕ}
    (hI : ∀ i ∈ I, i ≤ r) (k : Fin r) :
    weylRep K k ∈ flagStabilizer r K I ↔ (k : ℕ) + 1 ∉ I :=
  (subflag_generation (K := K) (r := r) I hI).2.1 k

private theorem spUCited_flagStabilizer_le_iff {I J : Set ℕ}
    (hI : ∀ i ∈ I, i ≤ r) (hJ : J ⊆ Set.Icc 1 r) :
    flagStabilizer r K I ≤ flagStabilizer r K J ↔ J ⊆ I := by
  constructor
  · intro h j hj
    by_contra hjI
    obtain ⟨hj1, hjr⟩ := Set.mem_Icc.mp (hJ hj)
    set k : Fin r := ⟨j - 1, by omega⟩
    have hk1 : (k : ℕ) + 1 = j := by
      simp only [k, Fin.val_mk]
      omega
    have hmemI : weylRep K k ∈ flagStabilizer r K I :=
      (spUCited_mem_flagStabilizer_weylRep (K := K) (r := r) hI k).mpr (by rw [hk1]; exact hjI)
    have hnotJ : weylRep K k ∉ flagStabilizer r K J := by
      refine fun hmem => (spUCited_mem_flagStabilizer_weylRep (K := K) (r := r)
        (fun i hi => (Set.mem_Icc.mp (hJ hi)).2) k).mp hmem ?_
      rw [hk1]
      exact hj
    exact hnotJ (h hmemI)
  · intro hJI g hg
    exact mem_flagStabilizer.mpr fun i hi => mem_flagStabilizer.mp hg i (hJI hi)

private theorem spUCited_flagStabilizer_inj {I J : Set ℕ}
    (hI : I ⊆ Set.Icc 1 r) (hJ : J ⊆ Set.Icc 1 r)
    (h : flagStabilizer r K I = flagStabilizer r K J) : I = J := by
  have h1 : J ⊆ I :=
    (spUCited_flagStabilizer_le_iff (K := K) (r := r)
      (fun i hi => (Set.mem_Icc.mp (hI hi)).2) hJ).mp h.le
  have h2 : I ⊆ J :=
    (spUCited_flagStabilizer_le_iff (K := K) (r := r)
      (fun i hi => (Set.mem_Icc.mp (hJ hi)).2) hI).mp h.ge
  exact Set.Subset.antisymm h2 h1

theorem spUCited_borel_le_par :
    Subgroup.normalizer (unipotent r K : Set ↥(StatedSp r K)) ≤ spUCitedPar r K := by
  rw [normalizer_unipotent]
  simpa only [spUCitedPar] using
    (borelSubgroup_le_flagStabilizer (K := K) (r := r) (I := Set.Icc 2 r)
      (fun i hi => (Set.mem_Icc.mp hi).2))

theorem spUCited_not_par_le_normalizer (hr : 2 ≤ r) :
    ¬ spUCitedPar r K ≤
      Subgroup.normalizer (spUCitedRoot r K ⟨0, by omega⟩ : Set ↥(StatedSp r K)) := by
  intro h
  have hmem : weylRep K (⟨0, by omega⟩ : Fin r) ∈ spUCitedPar r K := by
    rw [spUCitedPar]
    refine (spUCited_mem_flagStabilizer_weylRep (I := Set.Icc 2 r) ?_ _).mpr ?_
    · intro i hi
      exact (Set.mem_Icc.mp hi).2
    · intro hcon
      rw [Set.mem_Icc] at hcon
      have hval : ((⟨0, by omega⟩ : Fin r) : ℕ) = 0 := rfl
      omega
  have hnotmem : weylRep K (⟨0, by omega⟩ : Fin r) ∉
      Subgroup.normalizer (spUCitedRoot r K ⟨0, by omega⟩ : Set ↥(StatedSp r K)) := by
    rw [spUCited_normalizer_root_zero hr]
    exact weylRep_notMem_stabilizer (K := K) (r := r) (⟨0, by omega⟩ : Fin r)
  exact hnotmem (h hmem)

theorem spUCited_maximal (hr : 2 ≤ r) (M : Subgroup ↥(StatedSp r K))
    (hM : Subgroup.normalizer (spUCitedRoot r K ⟨0, by omega⟩ : Set ↥(StatedSp r K)) ≤ M) :
    M = Subgroup.normalizer (spUCitedRoot r K ⟨0, by omega⟩ : Set ↥(StatedSp r K)) ∨ M = ⊤ := by
  rw [spUCited_normalizer_root_zero hr] at hM ⊢
  exact eq_of_stabilizer_flag_le (d := 1) (by omega) M hM

theorem spUCited_cover (hr : 2 ≤ r) (A : Subgroup ↥(StatedSp r K))
    (hBA : Subgroup.normalizer (unipotent r K : Set ↥(StatedSp r K)) ≤ A)
    (hAP : A ≤ spUCitedPar r K) :
    A = Subgroup.normalizer (unipotent r K : Set ↥(StatedSp r K)) ∨ A = spUCitedPar r K := by
  have hBA' : borelSubgroup r K ≤ A := by
    rwa [normalizer_unipotent] at hBA
  obtain ⟨hAI, -⟩ := borel_overgroups A hBA'
  have hJtop : borelCuts K A ⊆ Set.Icc 1 r :=
    fun i hi => Set.mem_Icc.mpr (borelCuts_le A i hi)
  have hI0J : Set.Icc 2 r ⊆ borelCuts K A := by
    refine (spUCited_flagStabilizer_le_iff (K := K) (r := r) (I := borelCuts K A) (J := Set.Icc 2 r)
      (fun i hi => (borelCuts_le A i hi).2) ?_).mp ?_
    · exact Set.Icc_subset_Icc (by omega) le_rfl
    · rw [← hAI]
      simpa only [spUCitedPar] using hAP
  by_cases h1 : 1 ∈ borelCuts K A
  · left
    have hJeq : borelCuts K A = Set.Icc 1 r := by
      refine Set.Subset.antisymm hJtop ?_
      intro i hi
      obtain ⟨hi1, hir⟩ := Set.mem_Icc.mp hi
      by_cases hi1' : i = 1
      · exact hi1'.symm ▸ h1
      · exact hI0J (Set.mem_Icc.mpr ⟨by omega, hir⟩)
    calc A = flagStabilizer r K (borelCuts K A) := hAI
      _ = flagStabilizer r K (Set.Icc 1 r) := by rw [hJeq]
      _ = borelSubgroup r K := spUCited_borel_eq.symm
      _ = Subgroup.normalizer (unipotent r K : Set ↥(StatedSp r K)) := normalizer_unipotent.symm
  · right
    have hJeq : borelCuts K A = Set.Icc 2 r := by
      refine Set.Subset.antisymm ?_ hI0J
      intro i hi
      obtain ⟨hi1, hir⟩ := borelCuts_le A i hi
      have hi2 : 2 ≤ i := by
        by_contra h2
        have hieq : i = 1 := by omega
        exact h1 (hieq ▸ hi)
      exact Set.mem_Icc.mpr ⟨hi2, hir⟩
    calc A = flagStabilizer r K (borelCuts K A) := hAI
      _ = flagStabilizer r K (Set.Icc 2 r) := by rw [hJeq]
      _ = spUCitedPar r K := rfl

theorem spUCited_unique_cover (hr : 2 ≤ r) (P' : Subgroup ↥(StatedSp r K))
    (hBP : Subgroup.normalizer (unipotent r K : Set ↥(StatedSp r K)) ≤ P')
    (hcov : ∀ A : Subgroup ↥(StatedSp r K),
      Subgroup.normalizer (unipotent r K : Set ↥(StatedSp r K)) ≤ A → A ≤ P' →
        A = Subgroup.normalizer (unipotent r K : Set ↥(StatedSp r K)) ∨ A = P')
    (hnot : ¬ P' ≤
      Subgroup.normalizer (spUCitedRoot r K ⟨0, by omega⟩ : Set ↥(StatedSp r K))) :
    P' = spUCitedPar r K := by
  have hBP' : borelSubgroup r K ≤ P' := by
    rwa [normalizer_unipotent] at hBP
  obtain ⟨hP'I, -⟩ := borel_overgroups P' hBP'
  have hJtop : borelCuts K P' ⊆ Set.Icc 1 r :=
    fun i hi => Set.mem_Icc.mpr (borelCuts_le P' i hi)
  have hnot1 : 1 ∉ borelCuts K P' := by
    intro h1J
    apply hnot
    rw [hP'I, spUCited_normalizer_root_zero hr]
    exact fun g hg => mem_flagStabilizer.mp hg 1 h1J
  have hJI0 : borelCuts K P' ⊆ Set.Icc 2 r := by
    intro i hi
    obtain ⟨hi1, hir⟩ := borelCuts_le P' i hi
    refine Set.mem_Icc.mpr ⟨?_, hir⟩
    by_contra h2
    have hieq : i = 1 := by omega
    exact hnot1 (hieq ▸ hi)
  by_cases hJeq : borelCuts K P' = Set.Icc 2 r
  · calc P' = flagStabilizer r K (borelCuts K P') := hP'I
      _ = flagStabilizer r K (Set.Icc 2 r) := by rw [hJeq]
      _ = spUCitedPar r K := rfl
  · obtain ⟨i, hiI0, hiJ⟩ :=
      Set.not_subset.mp (fun hsub => hJeq (Set.Subset.antisymm hJI0 hsub))
    have hi1 : 1 ≤ i := by
      have h2 : 2 ≤ i := (Set.mem_Icc.mp hiI0).1
      omega
    have hir : i ≤ r := (Set.mem_Icc.mp hiI0).2
    have hUIcc : borelCuts K P' ∪ {i} ⊆ Set.Icc 1 r := by
      intro x hx
      rcases hx with hx | hx
      · exact hJtop hx
      · rw [Set.mem_singleton_iff] at hx
        subst hx
        exact Set.mem_Icc.mpr ⟨hi1, hir⟩
    have hBA : borelSubgroup r K ≤ flagStabilizer r K (borelCuts K P' ∪ {i}) :=
      borelSubgroup_le_flagStabilizer (K := K) (r := r) (fun x hx => (Set.mem_Icc.mp (hUIcc hx)).2)
    have hAP : flagStabilizer r K (borelCuts K P' ∪ {i}) ≤ P' := by
      calc flagStabilizer r K (borelCuts K P' ∪ {i})
          ≤ flagStabilizer r K (borelCuts K P') :=
            (spUCited_flagStabilizer_le_iff (K := K) (r := r)
              (I := borelCuts K P' ∪ {i}) (J := borelCuts K P')
              (fun x hx => (Set.mem_Icc.mp (hUIcc hx)).2) hJtop).mpr (fun x hx => Or.inl hx)
        _ = P' := hP'I.symm
    have hAneP : flagStabilizer r K (borelCuts K P' ∪ {i}) ≠ P' := by
      intro h
      have hst : flagStabilizer r K (borelCuts K P' ∪ {i}) =
          flagStabilizer r K (borelCuts K P') := by
        calc flagStabilizer r K (borelCuts K P' ∪ {i}) = P' := h
          _ = flagStabilizer r K (borelCuts K P') := hP'I
      have hUeq := spUCited_flagStabilizer_inj hUIcc hJtop hst
      have hiJ' : i ∈ borelCuts K P' := by
        have : i ∈ borelCuts K P' ∪ {i} := Or.inr (Set.mem_singleton i)
        rwa [hUeq] at this
      exact hiJ hiJ'
    have hAneB : flagStabilizer r K (borelCuts K P' ∪ {i}) ≠
        Subgroup.normalizer (unipotent r K : Set ↥(StatedSp r K)) := by
      intro h
      have hst : flagStabilizer r K (borelCuts K P' ∪ {i}) =
          flagStabilizer r K (Set.Icc 1 r) := by
        calc flagStabilizer r K (borelCuts K P' ∪ {i}) =
              Subgroup.normalizer (unipotent r K : Set ↥(StatedSp r K)) := h
          _ = borelSubgroup r K := normalizer_unipotent
          _ = flagStabilizer r K (Set.Icc 1 r) := spUCited_borel_eq
      have hUeq := spUCited_flagStabilizer_inj hUIcc (fun x hx => hx) hst
      have h1in : (1 : ℕ) ∈ borelCuts K P' ∪ {i} := by
        rw [hUeq]
        exact Set.mem_Icc.mpr ⟨le_refl 1, by omega⟩
      rcases h1in with h1J | h1i
      · exact hnot1 h1J
      · rw [Set.mem_singleton_iff] at h1i
        have h2 : 2 ≤ i := (Set.mem_Icc.mp hiI0).1
        omega
    have hAnorm : Subgroup.normalizer (unipotent r K : Set ↥(StatedSp r K)) ≤
        flagStabilizer r K (borelCuts K P' ∪ {i}) := by
      rwa [normalizer_unipotent]
    rcases hcov (flagStabilizer r K (borelCuts K P' ∪ {i})) hAnorm hAP with hA | hA
    · exact absurd hA hAneB
    · exact absurd hA hAneP

theorem spUCited_invariant (hr : 2 ≤ r) (α : MulAut ↥(StatedSp r K))
    (hU : Subgroup.map α.toMonoidHom (unipotent r K) = unipotent r K)
    (hR : Subgroup.map α.toMonoidHom (spUCitedRoot r K ⟨0, by omega⟩) =
      spUCitedRoot r K ⟨0, by omega⟩) :
    Subgroup.map α.toMonoidHom (spUCitedPar r K) = spUCitedPar r K :=
  spUCited_map_eq_of_unique_cover (U := unipotent r K)
    (R := spUCitedRoot r K ⟨0, by omega⟩) (P := spUCitedPar r K)
    spUCited_borel_le_par (spUCited_cover hr) (spUCited_not_par_le_normalizer hr)
    (fun P' h1 h2 h3 => spUCited_unique_cover hr P' h1 h2 h3) α hU hR

end CFSG.LocalAnalysis.WeakClosure81

end
