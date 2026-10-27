module

public import CFSG.LocalAnalysis.UniqueFourCatalog.OddClassicalGeneric
public import CFSG.LocalAnalysis.UniqueFourCatalog.Unitary
public import CFSG.LocalAnalysis.UniqueFourCatalog.Standing4Basic
public import CFSG.RankThree.PartTwo.Census.OddClassical.SymplecticComponent
public import CFSG.ClassicalInvolution.Models.SymplecticPairs.Complement
public import CFSG.Adapters.ClassicalCatalogReverse
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

open CFSG.Open
open CFSG.Yardstones.Mf4cdcdf2e013 (Standing4)

public section

namespace CFSG.LocalAnalysis.UniqueFourCatalog

section PSpBlock

open Matrix CFSG.ClassicalInvolution.Models.SymplecticPairs CFSG.Assembly.LowTwoRank
open CFSG.LieType.Universal.Symplectic.SpExtras (mat)
open scoped MatrixGroups

variable {K : Type} [Field K] {m : ℕ}

theorem longInv_not_mem_scalars (h2 : (2 : K) ≠ 0) (hm : 1 ≤ m) :
    longInv K (m + 1) 0 ∉ (StatedScalars (Fin (m + 1) ⊕ Fin (m + 1)) K).subgroupOf
      (StatedSp (m + 1) K) := by
  rintro ⟨u, hu⟩
  have hu' := congrArg (fun g : GL (Fin (m + 1) ⊕ Fin (m + 1)) K =>
    (g : Matrix (Fin (m + 1) ⊕ Fin (m + 1)) (Fin (m + 1) ⊕ Fin (m + 1)) K)) hu
  have hmat : (((longInv K (m + 1) 0 : StatedSp (m + 1) K) : GL (Fin (m + 1) ⊕ Fin (m + 1)) K) :
      Matrix (Fin (m + 1) ⊕ Fin (m + 1)) (Fin (m + 1) ⊕ Fin (m + 1)) K) =
      Matrix.diagonal (fun a => if a ∈ coords (0 : Fin (m + 1)) then (-1 : K) else 1) :=
    mat_longInv 0
  change Matrix.scalar _ (u : K) = (((longInv K (m + 1) 0 : StatedSp (m + 1) K) :
    GL (Fin (m + 1) ⊕ Fin (m + 1)) K) :
    Matrix (Fin (m + 1) ⊕ Fin (m + 1)) (Fin (m + 1) ⊕ Fin (m + 1)) K) at hu'
  rw [hmat] at hu'
  have e0 : (u : K) = -1 := by
    have := congrArg (fun M : Matrix (Fin (m + 1) ⊕ Fin (m + 1)) (Fin (m + 1) ⊕ Fin (m + 1)) K =>
      M (Sum.inl 0) (Sum.inl 0)) hu'
    simpa [inl_mem_coords] using this
  have e1 : (u : K) = 1 := by
    have := congrArg (fun M : Matrix (Fin (m + 1) ⊕ Fin (m + 1)) (Fin (m + 1) ⊕ Fin (m + 1)) K =>
      M (Sum.inl ⟨1, by omega⟩) (Sum.inl ⟨1, by omega⟩)) hu'
    have hn : (Sum.inl (⟨1, by omega⟩ : Fin (m + 1)) : Fin (m + 1) ⊕ Fin (m + 1)) ∉
        coords (0 : Fin (m + 1)) := by
      intro h
      rcases mem_coords.1 h with h | h
      · have := congrArg Fin.val (Sum.inl_injective h)
        simp at this
      · exact absurd h Sum.inl_ne_inr
    simpa [hn] using this
  exact h2 (by linear_combination e0 - e1)

theorem longInv_sq (n : ℕ) (k : Fin n) : longInv K n k ^ 2 = 1 := by
  rw [longInv, ← map_pow, neg_one_sq, map_one]

theorem longInv_mem_suppGroup (n : ℕ) (k : Fin n) :
    longInv K n k ∈ suppGroup (coords k) := by
  rw [← range_longBlock]
  exact ⟨-1, rfl⟩

theorem not_isCharTwoType_PSp_block [Finite K] (hr : 3 ≤ m + 1) (hodd : Odd (Nat.card K)) :
    ¬ IsCharTwoType (StatedProj (StatedSp (m + 1) K)) := by
  have h2 : (2 : K) ≠ 0 := CFSG.Semidihedral.OddFieldSL2.two_ne_zero_of_odd_card K hodd
  have hm : 2 ≤ m := by omega
  obtain ⟨e⟩ := nonempty_mulEquiv_complGroup_longInv h2 (0 : Fin (m + 1))
  have hF : (Infinite K ∨ 4 ≤ Nat.card K) ∨ (Nat.card K = 3 ∧ 2 ≤ m) ∨
      (Nat.card K = 2 ∧ 3 ≤ m) := by
    obtain ⟨k, hk⟩ := hodd
    have : 2 ≤ Nat.card K := by
      have := Nat.card_pos (α := K)
      have h1 : Nontrivial K := inferInstance
      have : 1 < Nat.card K := Finite.one_lt_card
      omega
    by_cases h3 : Nat.card K = 3
    · exact Or.inr (Or.inl ⟨h3, hm⟩)
    · exact Or.inl (Or.inr (by omega))
  have hqS := CFSG.LieType.Universal.Symplectic.isQuasisimple (n := m) (F := K) (by omega) hF
  have hq : CFSG.Open.IsQuasisimple ↥(complGroup (longInv K (m + 1) 0)) :=
    CFSG.Open.IsQuasisimple.of_mulEquiv e.symm ⟨hqS.1.commutator_eq_top, hqS.2.1⟩
  refine not_isCharTwoType_quotient_of_quasisimple
    ((StatedScalars (Fin (m + 1) ⊕ Fin (m + 1)) K).subgroupOf _)
    (CFSG.Open.StatedAPI.statedScalars_subgroupOf_le_center _) (t := longInv K (m + 1) 0)
    (longInv_not_mem_scalars h2 (by omega)) ?_ (J := complGroup (longInv K (m + 1) 0)) ?_ ?_
    ?_ hq
  · rw [longInv_sq]
    exact Subgroup.one_mem _
  · intro j hj
    rw [complGroup_longInv h2] at hj
    exact (commute_suppGroup_compl (longInv_mem_suppGroup (m + 1) 0) hj).symm.eq
  · intro g hg j hj
    have h1 : g⁻¹ * longInv K (m + 1) 0 * g⁻¹⁻¹ = longInv K (m + 1) 0 := by
      rw [inv_inv, mul_assoc, ← hg, ← mul_assoc, inv_mul_cancel, one_mul]
    have h3 := (mem_complGroup_conj (i := longInv K (m + 1) 0) (g := g⁻¹) (x := j)).1
      (by rw [h1]; exact hj)
    simpa [inv_inv] using h3
  · rw [eq_bot_iff]
    intro x hx
    obtain ⟨hxJ, hxN⟩ := Subgroup.mem_inf.mp hx
    obtain ⟨u, hu⟩ := Subgroup.mem_subgroupOf.mp hxN
    have hv : (Pi.single (Sum.inl 0) (1 : K) : Fin (m + 1) ⊕ Fin (m + 1) → K) ∈
        minusSpace (longInv K (m + 1) 0) := by
      rw [mem_minusSpace_longInv h2]
      intro a ha
      have : a ≠ Sum.inl 0 := fun h => ha (h ▸ inl_mem_coords 0)
      simp [this]
    have hfix := mem_complGroup.1 hxJ _ hv
    have hmx : mat (m + 1) K x = Matrix.scalar _ (u : K) :=
      (congrArg (fun g : GL (Fin (m + 1) ⊕ Fin (m + 1)) K =>
        (g : Matrix (Fin (m + 1) ⊕ Fin (m + 1)) (Fin (m + 1) ⊕ Fin (m + 1)) K)) hu).symm
    rw [hmx, Matrix.scalar_apply, Matrix.diagonal_mulVec_single] at hfix
    have hu1 : (u : K) = 1 := by
      have := congrFun hfix (Sum.inl 0)
      simpa using this
    have hu1' : u = 1 := Units.ext hu1
    have hx1 : x = 1 := by
      apply Subtype.ext
      rw [← hu, hu1', map_one]
      rfl
    rw [hx1]
    exact Subgroup.one_mem _

end PSpBlock

section PSpTag

open CFSG.RankThree.PartTwo.Census (not_isCharTwoType_PSp_two)

variable {G : Type} [Group G] [Finite G]

theorem not_uniqueFour_of_statedPSp_odd (hS : Standing4 G) {n p f : ℕ} (hp : p ≠ 2)
    (h : StatedClassicalModel G .PSp n p f) : ¬ uniqueFourUnique G := by
  have h' := h
  obtain ⟨⟨hpp, hf, hn2, hn22⟩, K, hKf, hKfin, hcard, ⟨e⟩⟩ := h
  have hqodd : Odd (p ^ f) := (hpp.odd_of_ne_two hp).pow
  have hodd : Odd (Nat.card K) := by rw [hcard]; exact hqodd
  by_cases hn : n = 2
  · subst hn
    by_cases hq3 : p ^ f = 3
    · obtain ⟨rfl, rfl⟩ := CFSG.ClassicalModels.eq_three_one_of_pow_eq_three hpp hf hq3
      exact not_uniqueFour_of_statedPSU hS
        (CFSG.ClassicalModels.statedClassicalModel_PSU_four_two_of_PSp_two_three h')
    · intro _
      have h4 : 4 ≤ Nat.card K := by
        have h1 : 1 < p ^ f := Nat.one_lt_pow (by omega) hpp.one_lt
        obtain ⟨k, hk⟩ := hqodd
        rw [hcard]
        omega
      exact hS.false_of_not_isCharTwoType e (not_isCharTwoType_PSp_two h4 hodd)
  · intro _
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    exact hS.false_of_not_isCharTwoType e (not_isCharTwoType_PSp_block (by omega) hodd)

end PSpTag

end CFSG.LocalAnalysis.UniqueFourCatalog
