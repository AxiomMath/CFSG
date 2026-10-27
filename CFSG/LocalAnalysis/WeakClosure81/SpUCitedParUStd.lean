module

public import CFSG.LocalAnalysis.WeakClosure81.SpUCitedParUNormal
public import CFSG.LocalAnalysis.WeakClosure81.SpUCitedParUCover
public import CFSG.LocalAnalysis.WeakClosure81.SpUCitedParAbs

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LinearGroups
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher

variable {K : Type} [Field K] {r ε : ℕ}

theorem uCited_rootParabolic_std {f : ℕ} (h : UnitaryFieldData 2 f K) (hr : 2 ≤ r)
    (hε : ε ≤ 1) :
    RootParabolic
      (uCitedRoot h r ε (Pi.single (Sum.inl (⟨0, by omega⟩ : Fin r)) (1 : K)))
      (hypUnitriangular h r ε)
      (uCitedRoot h r ε (Pi.single (Sum.inl (⟨1, by omega⟩ : Fin r)) (1 : K)))
      (uCitedPar h r ε) 2 := by
  haveI := h.finite
  haveI : Finite ↥(hypSU h r ε) := inferInstance
  obtain ⟨c, hc, hc0⟩ := exists_mem_traceZero_ne_zero' h
  have hU : ∃ T : Sylow 2 ↥(hypSU h r ε),
      (T : Subgroup ↥(hypSU h r ε)) = hypUnitriangular h r ε :=
    (unitary_order_and_Sylow h (p := 2) (by omega) hε).2.1
  have hUP : hypUnitriangular h r ε ≤ uCitedPar h r ε :=
    (Subgroup.le_normalizer (H := hypUnitriangular h r ε)).trans
      (uCited_normalizer_le_par h (by omega) hε)
  have hUR : hypUnitriangular h r ε ≤
      Subgroup.normalizer (uCitedRoot h r ε
        (Pi.single (Sum.inl (⟨0, by omega⟩ : Fin r)) (1 : K)) :
          Set ↥(hypSU h r ε)) := by
    rw [uCited_normalizer_root_zero h hr hε]
    exact (hypUnitriangular_le_hypBorel h).trans
      (hypBorel_le_isoStabilizer h (d := 1) (by omega) (by omega))
  have hn : uWeylRep ε h (⟨0, by omega⟩ : Fin r) c hc ∈ uCitedPar h r ε :=
    uCited_weylRep_zero_mem_par h hε hr hc hc0
  refine
    { mem := uCited_mem_rootGroupsIn h hr
      index := ?_
      one_le := by norm_num
      le := hUP
      isPGroup := ?_
      normal := uCited_normal h hr hε
      largest := ?_
      not_le := uCited_not_par_le_normalizer h hr hε
      maximal := uCited_maximal h hr hε
      invariant := uCited_invariant h hr hε }
  · have hv0 : (Pi.single (Sum.inl (⟨0, by omega⟩ : Fin r)) (1 : K) :
        HypIndex r ε → K) ≠ 0 := by
      intro hzero
      have := congrFun hzero (Sum.inl (⟨0, by omega⟩ : Fin r))
      simpa using this
    have hv : hypForm h r ε (Pi.single (Sum.inl (⟨0, by omega⟩ : Fin r)) (1 : K))
        (Pi.single (Sum.inl (⟨0, by omega⟩ : Fin r)) (1 : K)) = 0 :=
      hypForm_single_inl_self h ⟨0, by omega⟩
    calc (Subgroup.normalizer (uCitedRoot h r ε
            (Pi.single (Sum.inl (⟨1, by omega⟩ : Fin r)) (1 : K)) :
              Set ↥(hypSU h r ε))).relIndex (hypUnitriangular h r ε)
        ≤ Nat.card K := uCited_index_le h hr hε
      _ = 2 ^ (2 * f) := h.card
      _ = (2 ^ f) ^ 2 := pow_mul' 2 2 f
      _ = (Nat.card (uCitedRoot h r ε
            (Pi.single (Sum.inl (⟨0, by omega⟩ : Fin r)) (1 : K)))) ^ 2 := by
          rw [card_uCitedRoot h hv0 hv, UnitaryFieldData.card_traceZero h]
  · obtain ⟨T, hT⟩ := hU
    exact (hT ▸ T.isPGroup').to_inf_left
  · intro N hNP hN hN2
    have hmain := spUCited_le_inf_normalizer_of_normal (G := ↥(hypSU h r ε))
      hU hUR hUP hn hNP hN hN2
    rwa [uCited_conj_root_zero h hr hc hc0] at hmain

end CFSG.LocalAnalysis.WeakClosure81

end
