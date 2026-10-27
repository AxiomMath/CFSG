module

public import CFSG.RankThree.PartTwo.Sec4.Ronan148RH1Crit
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.Census228Spor.J3
public import CFSG.RankThree.PartTwo.Sec21.Item228CensusProofSpor

public section

namespace CFSG.RankThree.PartTwo.Sec4.Ronan148R

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4
open CFSG.RankThree.PartTwo.Sec4.RonanK429 CFSG.RankThree.PartTwo.Sec4.RonanK429H
open CFSG.RankThree.PartTwo.Sec4.Ronan148S
open CFSG.RankThree.PartTwo.KFacts.K426 CFSG.Sporadic.Schreier
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)
open Subgroup

section J3


theorem good427_j3XA :
    Good427 (centralizer ({j3tXA} : Set (Equiv.Perm (Fin 6156))) ⊓ j3P) := by
  obtain ⟨eD⟩ := CFSG.AGLEmbeddingD2.Wilson.Census228Spor.nonempty_mulEquiv_D_alt6
  haveI : IsSimpleGroup (alternatingGroup (Fin 6)) :=
    alternatingGroup.isSimpleGroup (by rw [Nat.card_eq_fintype_card, Fintype.card_fin]; norm_num)
  haveI : IsSimpleGroup (closure (Set.range j3tD)) := eD.isSimpleGroup
  have hDC : closure (Set.range j3tD) ≤
      centralizer ({j3tXA} : Set (Equiv.Perm (Fin 6156))) ⊓ j3P :=
    le_inf CFSG.AGLEmbeddingD2.Wilson.Census228Spor.closure_j3tD_le_centralizer (by
      rw [closure_le]
      rintro _ ⟨i, rfl⟩
      exact j3tD_mem i)
  have hder : ⁅centralizer ({j3tXA} : Set (Equiv.Perm (Fin 6156))) ⊓ j3P,
      centralizer ({j3tXA} : Set (Equiv.Perm (Fin 6156))) ⊓ j3P⁆ ≤ closure (Set.range j3tD) :=
    j3t_derived.1
  have hna : ∃ a b : closure (Set.range j3tD), a * b ≠ b * a := by
    have ha : (Equiv.swap (0 : Fin 6) 1 * Equiv.swap 0 2) ∈ alternatingGroup (Fin 6) := by
      rw [Equiv.Perm.mem_alternatingGroup]; decide
    have hb : (Equiv.swap (0 : Fin 6) 1 * Equiv.swap 2 3) ∈ alternatingGroup (Fin 6) := by
      rw [Equiv.Perm.mem_alternatingGroup]; decide
    refine ⟨eD.symm ⟨_, ha⟩, eD.symm ⟨_, hb⟩, fun h => ?_⟩
    have h' := congrArg (fun z => ((eD z : alternatingGroup (Fin 6)) : Equiv.Perm (Fin 6))) h
    simp only [map_mul, MulEquiv.apply_symm_apply, Subgroup.coe_mul] at h'
    revert h'
    decide
  exact good427_of_derived_le_simple hDC hna (by rw [j3t_derived.2]; norm_num) hder

theorem good427_j3P (x : Equiv.Perm (Fin 6156)) (hx : x ∈ j3P) (hxo : orderOf x = 3) :
    Good427 (centralizer ({x} : Set (Equiv.Perm (Fin 6156))) ⊓ j3P) := by
  obtain ⟨k, hk, c, hc, e, he, rfl⟩ := j3t_fusion hx hxo
  rcases hc with rfl | rfl
  · exact Good427.conj hk (j3tReps_spec (c := 0) (by norm_num)).2 he good427_j3XA
  · refine Good427.conj hk (j3tReps_spec (c := 1) (by norm_num)).2 he
      (good427_of_card_dvd (M := 243) ?_ (by norm_num))
    have h := j3t_caseB
    rw [h.1] at h
    exact dvd_of_eq h.2

theorem noCfgS427_j3 :
    ∀ (S : Type) [Group S] [Finite S], IsSimpleGroup S → (∃ a b : S, a * b ≠ b * a) →
      Nonempty (S ≃* Blueprint.NativeSporadic.Carrier .J3) → NoCfgS427 S ∧ NoONS427 S := by
  intro S _ _ _ hna ⟨e⟩
  haveI : Finite (Blueprint.NativeSporadic.Carrier .J3) := Finite.of_equiv S e.toEquiv
  have hcard : Nat.card S = 50232960 :=
    (Nat.card_congr e.toEquiv).trans CFSG.Sporadic.J3.card_J3
  refine ⟨noCfgS427_of_subgroupModel (e.trans Sec21.Item228CensusProof.j3CarrierEquiv)
    (RonanK429H.center_eq_bot_of_simple_nonab hna)
    (not_three_dvd_outer_of_mulEquiv e (not_three_dvd_outer_of_le_two card_outer_J3)) good427_j3P,
    noONS427_of_card (by rw [hcard]; norm_num)⟩

end J3

section Rows



theorem rowOf427_j3
    : RowOf427 (Spor .J3) :=
  rowOf427_spor (s := .J3) CFSG.Sporadic.Bridge.J3.nonempty_mulEquiv noCfgS427_j3

end Rows

end CFSG.RankThree.PartTwo.Sec4.Ronan148R

end
