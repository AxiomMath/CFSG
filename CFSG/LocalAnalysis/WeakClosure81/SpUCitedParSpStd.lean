module

public import CFSG.LocalAnalysis.WeakClosure81.SpUCitedParSpNormal
public import CFSG.LocalAnalysis.WeakClosure81.SpUCitedParSpCover
public import CFSG.LocalAnalysis.WeakClosure81.SpUCitedParAbs

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Open CFSG.RankThree.PartOne.KCSpFull CFSG.RankThree.Classical
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher

variable {r : ℕ} {K : Type} [Field K]

theorem spUCited_weylRep_zero_mem_par (hr : 2 ≤ r) :
    weylRep K (⟨0, by omega⟩ : Fin r) ∈ spUCitedPar r K := by
  rw [spUCitedPar]
  exact ((subflag_generation (r := r) (K := K) (Set.Icc 2 r)
    (fun i hi => hi.2)).2.1 ⟨0, by omega⟩).mpr (by simp [Set.mem_Icc])

theorem spUCited_rootParabolic_std [Finite K] [CharP K 2] (hr : 2 ≤ r) :
    RootParabolic (spUCitedRoot r K ⟨0, by omega⟩) (unipotent r K)
      (spUCitedRoot r K ⟨1, by omega⟩) (spUCitedPar r K) 1 := by
  haveI : Finite ↥(StatedSp r K) := inferInstance
  have hU : ∃ T : Sylow 2 ↥(StatedSp r K),
      (T : Subgroup ↥(StatedSp r K)) = unipotent r K :=
    exists_sylow_unipotent (K := K) (p := 2) (r := r)
  have hUR : unipotent r K ≤
      Subgroup.normalizer (spUCitedRoot r K ⟨0, by omega⟩ : Set ↥(StatedSp r K)) := by
    rw [spUCited_normalizer_root_zero hr]
    exact unipotent_le_borelSubgroup.trans
      (borelSubgroup_le_stabilizer_flag (K := K) (r := r) (d := 1) (by omega))
  have hUP : unipotent r K ≤ spUCitedPar r K :=
    (Subgroup.le_normalizer (H := unipotent r K)).trans spUCited_borel_le_par
  have hn : weylRep K ⟨0, by omega⟩ ∈ spUCitedPar r K :=
    spUCited_weylRep_zero_mem_par hr
  refine
    { mem := spUCited_mem_rootGroupsIn hr
      index := ?_
      one_le := le_refl 1
      le := hUP
      isPGroup := ?_
      normal := spUCited_normal hr
      largest := ?_
      not_le := spUCited_not_par_le_normalizer hr
      maximal := spUCited_maximal hr
      invariant := spUCited_invariant hr }
  · calc (Subgroup.normalizer
            (spUCitedRoot r K ⟨1, by omega⟩ : Set ↥(StatedSp r K))).relIndex
          (unipotent r K)
        ≤ Nat.card K := spUCited_index_le hr
      _ = Nat.card (spUCitedRoot r K ⟨0, by omega⟩) :=
          (spUCited_card_root (K := K) (r := r) (i := ⟨0, by omega⟩)).symm
      _ = (Nat.card (spUCitedRoot r K ⟨0, by omega⟩)) ^ 1 := (pow_one _).symm
  · obtain ⟨T, hT⟩ := hU
    exact (hT ▸ T.isPGroup').to_inf_left
  · intro N hNP hN hN2
    have h := spUCited_le_inf_normalizer_of_normal (G := ↥(StatedSp r K))
      hU hUR hUP hn hNP hN hN2
    rwa [spUCited_conj_root_zero hr] at h

end CFSG.LocalAnalysis.WeakClosure81

end
