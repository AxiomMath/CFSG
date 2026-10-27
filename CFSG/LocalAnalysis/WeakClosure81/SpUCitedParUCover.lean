module

public import CFSG.LocalAnalysis.WeakClosure81.SpUCitedParUBasic2
public import CFSG.LocalAnalysis.WeakClosure81.SpUCitedParUPar
public import CFSG.LocalAnalysis.WeakClosure81.SpUCitedParLattice
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherMaximalParabolics

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LinearGroups
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher

variable {p f : ℕ} {K : Type} [Field K] {r ε : ℕ}

private theorem spUCited_uBorel_eq (h : UnitaryFieldData p f K) :
    hypBorel h r ε = flagStabilizer h r ε (Set.Icc 1 r) := by
  ext g
  rw [mem_hypBorel, mem_flagStabilizer]
  exact ⟨fun hg i hi => hg i hi.1 hi.2, fun hg i h1 h2 => hg i ⟨h1, h2⟩⟩

private theorem spUCited_uFlagStabilizer_le_iff (h : UnitaryFieldData p f K) (hε : ε ≤ 1)
    {I J : Set ℕ} (hI : I ⊆ Set.Icc 1 r) (hJ : J ⊆ Set.Icc 1 r) :
    flagStabilizer h r ε I ≤ flagStabilizer h r ε J ↔ J ⊆ I := by
  obtain ⟨c, hc, hc0⟩ := exists_mem_traceZero_ne_zero' h
  constructor
  · intro hle j hj
    by_contra hjI
    obtain ⟨hj1, hjr⟩ := Set.mem_Icc.mp (hJ hj)
    set k : Fin r := ⟨j - 1, by omega⟩
    have hk1 : (k : ℕ) + 1 = j := by
      simp only [k, Fin.val_mk]
      omega
    have hmemI : uWeylRep ε h k c hc ∈ flagStabilizer h r ε I :=
      (uWeylRep_mem_flagStabilizer_iff h hε hc hc0 hI k).mpr (by rw [hk1]; exact hjI)
    have hnotJ : uWeylRep ε h k c hc ∉ flagStabilizer h r ε J := by
      refine fun hmem => (uWeylRep_mem_flagStabilizer_iff h hε hc hc0 hJ k).mp hmem ?_
      rw [hk1]
      exact hj
    exact hnotJ (hle hmemI)
  · intro hJI g hg
    exact mem_flagStabilizer.mpr fun i hi => mem_flagStabilizer.mp hg i (hJI hi)

private theorem spUCited_uFlagStabilizer_inj (h : UnitaryFieldData p f K) (hε : ε ≤ 1)
    {I J : Set ℕ} (hI : I ⊆ Set.Icc 1 r) (hJ : J ⊆ Set.Icc 1 r)
    (heq : flagStabilizer h r ε I = flagStabilizer h r ε J) : I = J := by
  have h1 : J ⊆ I := (spUCited_uFlagStabilizer_le_iff h hε hI hJ).mp heq.le
  have h2 : I ⊆ J := (spUCited_uFlagStabilizer_le_iff h hε hJ hI).mp heq.ge
  exact Set.Subset.antisymm h2 h1

theorem uCited_normalizer_le_par (h : UnitaryFieldData p f K) (hr : 1 ≤ r) (hε : ε ≤ 1) :
    Subgroup.normalizer (hypUnitriangular h r ε : Set ↥(hypSU h r ε)) ≤ uCitedPar h r ε := by
  rw [normalizer_hypUnitriangular h hr hε]
  exact uCited_borel_le_par h

theorem uCited_not_par_le_normalizer (h : UnitaryFieldData p f K) (hr : 2 ≤ r) (hε : ε ≤ 1) :
    ¬ uCitedPar h r ε ≤
      Subgroup.normalizer (uCitedRoot h r ε (Pi.single (Sum.inl (⟨0, by omega⟩ : Fin r))
        (1 : K)) : Set ↥(hypSU h r ε)) := by
  obtain ⟨c, hc, hc0⟩ := exists_mem_traceZero_ne_zero' h
  intro hle
  have hmem : uWeylRep ε h (⟨0, by omega⟩ : Fin r) c hc ∈ uCitedPar h r ε :=
    uCited_weylRep_zero_mem_par h hε hr hc hc0
  have hnotmem : uWeylRep ε h (⟨0, by omega⟩ : Fin r) c hc ∉
      Subgroup.normalizer (uCitedRoot h r ε (Pi.single (Sum.inl (⟨0, by omega⟩ : Fin r))
        (1 : K)) : Set ↥(hypSU h r ε)) := by
    rw [uCited_normalizer_root_zero h hr hε]
    intro hmemiso
    exact (uWeylRep_smul_hypFlag h hε hc hc0 (⟨0, by omega⟩ : Fin r) (by omega)).mp
      (mem_isoStabilizer.mp hmemiso) rfl
  exact hnotmem (hle hmem)

theorem uCited_maximal (h : UnitaryFieldData p f K) (hr : 2 ≤ r) (hε : ε ≤ 1)
    (M : Subgroup ↥(hypSU h r ε))
    (hM : Subgroup.normalizer (uCitedRoot h r ε (Pi.single (Sum.inl (⟨0, by omega⟩ : Fin r))
      (1 : K)) : Set ↥(hypSU h r ε)) ≤ M) :
    M = Subgroup.normalizer (uCitedRoot h r ε (Pi.single (Sum.inl (⟨0, by omega⟩ : Fin r))
      (1 : K)) : Set ↥(hypSU h r ε)) ∨ M = ⊤ := by
  rw [uCited_normalizer_root_zero h hr hε] at hM ⊢
  exact eq_of_isoStabilizer_hypFlag_le h (by omega) hε (d := 1) le_rfl (by omega) M hM

theorem uCited_cover (h : UnitaryFieldData p f K) (hr : 2 ≤ r) (hε : ε ≤ 1)
    (A : Subgroup ↥(hypSU h r ε))
    (hBA : Subgroup.normalizer (hypUnitriangular h r ε : Set ↥(hypSU h r ε)) ≤ A)
    (hAP : A ≤ uCitedPar h r ε) :
    A = Subgroup.normalizer (hypUnitriangular h r ε : Set ↥(hypSU h r ε)) ∨
      A = uCitedPar h r ε := by
  have hBA' : hypBorel h r ε ≤ A := by
    rwa [normalizer_hypUnitriangular h (by omega) hε] at hBA
  obtain ⟨c, hc, hc0⟩ := exists_mem_traceZero_ne_zero' h
  obtain ⟨-, hAI, -, -⟩ := unitary_Borel_overgroups h (by omega) hε hc hc0 A hBA'
  have hJtop : overgroupCuts ε h c hc A ⊆ Set.Icc 1 r := overgroupCuts_subset h hc A
  have hIcc : Set.Icc 2 r ⊆ Set.Icc 1 r := by
    intro i hi
    obtain ⟨hi2, hir⟩ := Set.mem_Icc.mp hi
    exact Set.mem_Icc.mpr ⟨by omega, hir⟩
  have hI0J : Set.Icc 2 r ⊆ overgroupCuts ε h c hc A := by
    refine (spUCited_uFlagStabilizer_le_iff h hε hJtop hIcc).mp ?_
    rw [← hAI]
    simpa only [uCitedPar] using hAP
  by_cases h1 : 1 ∈ overgroupCuts ε h c hc A
  · left
    have hJeq : overgroupCuts ε h c hc A = Set.Icc 1 r := by
      refine Set.Subset.antisymm hJtop ?_
      intro i hi
      obtain ⟨hi1, hir⟩ := Set.mem_Icc.mp hi
      by_cases hi1' : i = 1
      · exact hi1'.symm ▸ h1
      · exact hI0J (Set.mem_Icc.mpr ⟨by omega, hir⟩)
    calc A = flagStabilizer h r ε (overgroupCuts ε h c hc A) := hAI
      _ = flagStabilizer h r ε (Set.Icc 1 r) := by rw [hJeq]
      _ = hypBorel h r ε := (spUCited_uBorel_eq h).symm
      _ = Subgroup.normalizer (hypUnitriangular h r ε : Set ↥(hypSU h r ε)) :=
            (normalizer_hypUnitriangular h (by omega) hε).symm
  · right
    have hJeq : overgroupCuts ε h c hc A = Set.Icc 2 r := by
      refine Set.Subset.antisymm ?_ hI0J
      intro i hi
      obtain ⟨hi1, hir⟩ := Set.mem_Icc.mp (hJtop hi)
      have hi2 : 2 ≤ i := by
        by_contra h2
        have hieq : i = 1 := by omega
        exact h1 (hieq ▸ hi)
      exact Set.mem_Icc.mpr ⟨hi2, hir⟩
    calc A = flagStabilizer h r ε (overgroupCuts ε h c hc A) := hAI
      _ = flagStabilizer h r ε (Set.Icc 2 r) := by rw [hJeq]
      _ = uCitedPar h r ε := rfl

theorem uCited_unique_cover (h : UnitaryFieldData p f K) (hr : 2 ≤ r) (hε : ε ≤ 1)
    (P' : Subgroup ↥(hypSU h r ε))
    (hBP : Subgroup.normalizer (hypUnitriangular h r ε : Set ↥(hypSU h r ε)) ≤ P')
    (hcov : ∀ A : Subgroup ↥(hypSU h r ε),
      Subgroup.normalizer (hypUnitriangular h r ε : Set ↥(hypSU h r ε)) ≤ A → A ≤ P' →
        A = Subgroup.normalizer (hypUnitriangular h r ε : Set ↥(hypSU h r ε)) ∨ A = P')
    (hnot : ¬ P' ≤ Subgroup.normalizer (uCitedRoot h r ε
      (Pi.single (Sum.inl (⟨0, by omega⟩ : Fin r)) (1 : K)) : Set ↥(hypSU h r ε))) :
    P' = uCitedPar h r ε := by
  have hBP' : hypBorel h r ε ≤ P' := by
    rwa [normalizer_hypUnitriangular h (by omega) hε] at hBP
  obtain ⟨c, hc, hc0⟩ := exists_mem_traceZero_ne_zero' h
  obtain ⟨-, hP'I, -, -⟩ := unitary_Borel_overgroups h (by omega) hε hc hc0 P' hBP'
  have hJtop : overgroupCuts ε h c hc P' ⊆ Set.Icc 1 r := overgroupCuts_subset h hc P'
  have hnot1 : 1 ∉ overgroupCuts ε h c hc P' := by
    intro h1J
    apply hnot
    rw [hP'I, uCited_normalizer_root_zero h hr hε]
    exact fun g hg => mem_isoStabilizer.mpr (mem_flagStabilizer.mp hg 1 h1J)
  have hJI0 : overgroupCuts ε h c hc P' ⊆ Set.Icc 2 r := by
    intro i hi
    obtain ⟨hi1, hir⟩ := Set.mem_Icc.mp (hJtop hi)
    refine Set.mem_Icc.mpr ⟨?_, hir⟩
    by_contra h2
    have hieq : i = 1 := by omega
    exact hnot1 (hieq ▸ hi)
  by_cases hJeq : overgroupCuts ε h c hc P' = Set.Icc 2 r
  · calc P' = flagStabilizer h r ε (overgroupCuts ε h c hc P') := hP'I
      _ = flagStabilizer h r ε (Set.Icc 2 r) := by rw [hJeq]
      _ = uCitedPar h r ε := rfl
  · obtain ⟨i, hiI0, hiJ⟩ :=
      Set.not_subset.mp (fun hsub => hJeq (Set.Subset.antisymm hJI0 hsub))
    have hi1 : 1 ≤ i := le_trans (by omega : 1 ≤ 2) (Set.mem_Icc.mp hiI0).1
    have hir : i ≤ r := (Set.mem_Icc.mp hiI0).2
    have hUIcc : overgroupCuts ε h c hc P' ∪ {i} ⊆ Set.Icc 1 r := by
      intro x hx
      rcases hx with hx | hx
      · exact hJtop hx
      · rw [Set.mem_singleton_iff] at hx
        subst hx
        exact Set.mem_Icc.mpr ⟨hi1, hir⟩
    have hBA : hypBorel h r ε ≤ flagStabilizer h r ε (overgroupCuts ε h c hc P' ∪ {i}) :=
      hypBorel_le_flagStabilizer hUIcc
    have hAP : flagStabilizer h r ε (overgroupCuts ε h c hc P' ∪ {i}) ≤ P' := by
      calc flagStabilizer h r ε (overgroupCuts ε h c hc P' ∪ {i})
          ≤ flagStabilizer h r ε (overgroupCuts ε h c hc P') :=
            (spUCited_uFlagStabilizer_le_iff h hε hUIcc hJtop).mpr (fun x hx => Or.inl hx)
        _ = P' := hP'I.symm
    have hAneP : flagStabilizer h r ε (overgroupCuts ε h c hc P' ∪ {i}) ≠ P' := by
      intro heqA
      have hst : flagStabilizer h r ε (overgroupCuts ε h c hc P' ∪ {i}) =
          flagStabilizer h r ε (overgroupCuts ε h c hc P') := by
        calc flagStabilizer h r ε (overgroupCuts ε h c hc P' ∪ {i}) = P' := heqA
          _ = flagStabilizer h r ε (overgroupCuts ε h c hc P') := hP'I
      have hUeq := spUCited_uFlagStabilizer_inj h hε hUIcc hJtop hst
      have hiJ' : i ∈ overgroupCuts ε h c hc P' := by
        have : i ∈ overgroupCuts ε h c hc P' ∪ {i} := Or.inr (Set.mem_singleton i)
        rwa [hUeq] at this
      exact hiJ hiJ'
    have hAneB : flagStabilizer h r ε (overgroupCuts ε h c hc P' ∪ {i}) ≠
        Subgroup.normalizer (hypUnitriangular h r ε : Set ↥(hypSU h r ε)) := by
      intro heqB
      have hst : flagStabilizer h r ε (overgroupCuts ε h c hc P' ∪ {i}) =
          flagStabilizer h r ε (Set.Icc 1 r) := by
        calc flagStabilizer h r ε (overgroupCuts ε h c hc P' ∪ {i}) =
              Subgroup.normalizer (hypUnitriangular h r ε : Set ↥(hypSU h r ε)) := heqB
          _ = hypBorel h r ε := normalizer_hypUnitriangular h (by omega) hε
          _ = flagStabilizer h r ε (Set.Icc 1 r) := spUCited_uBorel_eq h
      have hUeq := spUCited_uFlagStabilizer_inj h hε hUIcc (fun x hx => hx) hst
      have h1in : (1 : ℕ) ∈ overgroupCuts ε h c hc P' ∪ {i} := by
        rw [hUeq]
        exact Set.mem_Icc.mpr ⟨le_refl 1, by omega⟩
      rcases h1in with h1J | h1i
      · exact hnot1 h1J
      · rw [Set.mem_singleton_iff] at h1i
        have h2 : 2 ≤ i := (Set.mem_Icc.mp hiI0).1
        omega
    have hAnorm : Subgroup.normalizer (hypUnitriangular h r ε : Set ↥(hypSU h r ε)) ≤
        flagStabilizer h r ε (overgroupCuts ε h c hc P' ∪ {i}) := by
      rwa [normalizer_hypUnitriangular h (by omega) hε]
    rcases hcov (flagStabilizer h r ε (overgroupCuts ε h c hc P' ∪ {i})) hAnorm hAP with
      hA | hA
    · exact absurd hA hAneB
    · exact absurd hA hAneP

theorem uCited_invariant (h : UnitaryFieldData p f K) (hr : 2 ≤ r) (hε : ε ≤ 1)
    (α : MulAut ↥(hypSU h r ε))
    (hU : Subgroup.map α.toMonoidHom (hypUnitriangular h r ε) = hypUnitriangular h r ε)
    (hR : Subgroup.map α.toMonoidHom (uCitedRoot h r ε
      (Pi.single (Sum.inl (⟨0, by omega⟩ : Fin r)) (1 : K))) =
      uCitedRoot h r ε (Pi.single (Sum.inl (⟨0, by omega⟩ : Fin r)) (1 : K))) :
    Subgroup.map α.toMonoidHom (uCitedPar h r ε) = uCitedPar h r ε :=
  spUCited_map_eq_of_unique_cover (U := hypUnitriangular h r ε)
    (R := uCitedRoot h r ε (Pi.single (Sum.inl (⟨0, by omega⟩ : Fin r)) (1 : K)))
    (P := uCitedPar h r ε)
    (uCited_normalizer_le_par h (by omega) hε) (uCited_cover h hr hε)
    (uCited_not_par_le_normalizer h hr hε)
    (fun P' h1 h2 h3 => uCited_unique_cover h hr hε P' h1 h2 h3) α hU hR

end CFSG.LocalAnalysis.WeakClosure81

end
