module

public import CFSG.RankThree.Native.HSMcLSmall
public import CFSG.Sporadic.SmallOddCore.HSAut
public import CFSG.Sporadic.SmallOddCore.McLAut

public section

namespace CFSG.RankThree.Native

open Subgroup CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Certificates
  CFSG.Certificates.Native CFSG.Sporadic.Schreier CFSG.Sporadic.SmallOddCore
  CFSG.ComponentClassification.OuterAutomorphisms

theorem hs100P_transitive : ∀ x : Fin 100, ∃ g ∈ hs100P, g 0 = x := by
  have h0 : 0 < hs100Chain.baseCount := by decide
  have hsize : hs100Chain.orbitSize ⟨0, h0⟩ = 100 := by
    have h := List.getElem_of_eq hs100Chain_orbitSizes (i := 0) (by simp [h0])
    simpa only [List.getElem_map, List.getElem_finRange, List.getElem_cons_zero, Fin.cast_mk]
      using h
  intro x
  obtain ⟨g, hg, hgx⟩ := transitive_of_orbitSize hs100Chain hs100Chain_valid h0 hsize x
  refine ⟨g, by rw [hs100P_eq_original]; exact hg, ?_⟩
  have hb : hs100Chain.base.get ⟨0, h0⟩ = 0 := rfl
  rwa [hb] at hgx

theorem hs100Strong_mem {j : ℕ} (hj : j < 15) : permOfArr 100 (hs100Arr j) ∈ hs100P := by
  rw [hs100P_eq_original]
  apply hs100Chain.strong_mem_originalSubgroup hs100Chain_valid
  have hj' : j < hs100Chain.strongCount := by
    simpa [hs100Chain, RawSchreierDatum.ofArrays, hs100StrongArrs] using hj
  have e : hs100Chain.strong.get ⟨j, hj'⟩ = permOfArr 100 (hs100Arr j) := by
    rw [hs100Chain_strong_get]
    exact congrArg (permOfArr 100) (hs100StrongArrs_get hj)
  exact (schreier_vector_mem_toList_iff_get _ _).2 ⟨⟨j, hj'⟩, e⟩

theorem centralizer_hs100P : centralizer (hs100P : Set (Equiv.Perm (Fin 100))) = ⊥ := by
  refine centralizer_eq_bot_of_transitive 0 hs100P_transitive fun x hx => ?_
  have h := allLt_iff.1 hs100_chain_check.2.2.2.2 x x.2
  simp only [Bool.or_eq_true, beq_iff_eq, List.any_eq_true, List.mem_range, Bool.and_eq_true,
    bne_iff_ne, ne_eq] at h
  rcases h with h | ⟨j, hj, h0, hx'⟩
  · exact absurd (Fin.ext h) hx
  · have hrep := rep_hs100Arr hj
    rw [hs100StrongArrs_get hj] at h0 hx'
    refine ⟨permOfArr 100 (hs100Arr j), hs100Strong_mem hj, ?_, ?_⟩
    · apply Fin.ext
      rw [← hrep 0]
      exact h0
    · intro hfx
      apply hx'
      rw [hrep x, hfx]

theorem centralizer_mcl275P : centralizer (mcl275P : Set (Equiv.Perm (Fin 275))) = ⊥ :=
  mcl_normalizing_model.2.2.2.2.1

theorem center_eq_bot_of_centralizer {n : ℕ} {P : Subgroup (Equiv.Perm (Fin n))}
    (h : centralizer (P : Set (Equiv.Perm (Fin n))) = ⊥) : center P = ⊥ := by
  rw [eq_bot_iff]
  intro z hz
  have hzc : (z : Equiv.Perm (Fin n)) ∈ centralizer (P : Set (Equiv.Perm (Fin n))) := by
    rw [mem_centralizer_iff]
    intro p hp
    have := (mem_center_iff.1 hz) ⟨p, hp⟩
    exact congrArg Subtype.val this
  rw [h, mem_bot] at hzc
  rw [mem_bot]
  exact Subtype.ext hzc

theorem outer_card_hs100P : Nat.card (Outer hs100P) ≤ 2 := by
  rw [← Nat.card_congr (equivalence hsPStarEquiv).toEquiv]
  exact hs_outer_card_le

theorem outer_card_mcl275P : Nat.card (Outer mcl275P) ≤ 2 := mcl_outer_card_le

theorem CTUC_HS_McL_two_element_outer_automorphism_bounds :
    (center hs100P = ⊥ ∧ Nat.card (Outer hs100P) ≤ 2) ∧
      (center mcl275P = ⊥ ∧ Nat.card (Outer mcl275P) ≤ 2) :=
  ⟨⟨center_eq_bot_of_centralizer centralizer_hs100P, outer_card_hs100P⟩,
    ⟨center_eq_bot_of_centralizer centralizer_mcl275P, outer_card_mcl275P⟩⟩

end CFSG.RankThree.Native
