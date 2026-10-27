module

public import CFSG.RankThree.PartOne.KFCL.L4Torus
public import Mathlib.LinearAlgebra.Projectivization.PSL.PSL2
public import CFSG.RankThree.PartOne.KFCL.BlockSL

public section

namespace CFSG.RankThree.PartOne.KFCL.L4

open Matrix CFSG.RankThree.PartOne.KFCL.BlockSL
open scoped MatrixGroups

variable {K : Type} [Field K]

@[expose] def pairBlock (K : Type) [Field K] (s : Finset (Fin 4)) : Subgroup (SL(4, K)) :=
  (extHom1 (m := Fin 4) (K := K) (fun k => k ∈ s)).range

theorem mem_pairBlock_iff {s : Finset (Fin 4)} {g : SL(4, K)} :
    g ∈ pairBlock K s ↔
      ∀ a b : Fin 4, ¬ (a ∈ s ∧ b ∈ s) → g.1 a b = (1 : Matrix (Fin 4) (Fin 4) K) a b :=
  mem_range_extHom1_iff (fun k => k ∈ s) g

theorem transvection_mem_pairBlock {a b : Fin 4} (hab : a ≠ b) (c : K) :
    SpecialLinearGroup.transvection hab c ∈ pairBlock K {a, b} := by
  rw [mem_pairBlock_iff]
  intro x y hxy
  have : ¬ (a = x ∧ b = y) := fun ⟨h1, h2⟩ => hxy ⟨by simp [← h1], by simp [← h2]⟩
  simp [SpecialLinearGroup.transvection_coe, this]

theorem pairBlock_le_centralizer (p : ℕ) (s : Finset (Fin 4)) :
    pairBlock K s ≤ Subgroup.centralizer (hypSub p K s : Set (SL(4, K))) := by
  intro g hg
  rw [Subgroup.mem_centralizer_iff]
  intro h hh
  obtain ⟨⟨d, hd, -⟩, hs⟩ := hh
  have hg' := mem_pairBlock_iff.1 hg
  apply Subtype.ext
  ext a b
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, hd, Matrix.diagonal_mul,
    Matrix.mul_diagonal]
  by_cases hab : a = b
  · subst hab
    exact mul_comm _ _
  · by_cases hs2 : a ∈ s ∧ b ∈ s
    · have := hs a hs2.1 b hs2.2
      rw [hd, diagonal_apply_eq, diagonal_apply_eq] at this
      rw [this]
      exact mul_comm _ _
    · rw [hg' a b hs2, Matrix.one_apply_ne hab]
      simp

theorem sl2_isSimpleGroup [CharP K 2] (h4 : 4 ≤ Nat.card K) : IsSimpleGroup SL(2, K) := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have hc : Subgroup.center SL(2, K) = ⊥ := by
    refine eq_bot_iff.mpr fun A hA => ?_
    obtain ⟨r, hr, hrA⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hA
    rw [Fintype.card_fin] at hr
    have h5 : (r - 1) ^ 2 = 0 := by linear_combination hr + (1 - r) * h2
    have hr1 : r = 1 := sub_eq_zero.mp ((pow_eq_zero_iff two_ne_zero).mp h5)
    subst hr1
    rw [Subgroup.mem_bot]
    ext i j
    have := congrFun (congrFun hrA i) j
    simpa [Matrix.scalar_apply, Matrix.one_apply] using this.symm
  have : IsSimpleGroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) K) :=
    Matrix.ProjectiveSpecialLinearGroup.rank_two_simple h4
  have e : SL(2, K) ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) K :=
    QuotientGroup.quotientBot.symm.trans (QuotientGroup.quotientMulEquivOfEq hc.symm)
  exact e.isSimpleGroup

theorem isSimpleGroup_range_extHom1 {m : Type} [Fintype m] [DecidableEq m] (p : m → Prop) [DecidablePred p]
    [CharP K 2] (h4 : 4 ≤ Nat.card K) (hcard : Fintype.card {i // p i} = 2) :
    IsSimpleGroup ↥(extHom1 (K := K) p).range := by
  have hcard' : Fintype.card {i // p i} = Fintype.card (Fin 2) := by rw [hcard, Fintype.card_fin]
  let e : {i // p i} ≃ Fin 2 := Fintype.equivOfCardEq hcard'
  have e₁ : SpecialLinearGroup {i // p i} K ≃* ↥(extHom1 (K := K) p).range :=
    MonoidHom.ofInjective (extHom1_injective p)
  have e₂ : SpecialLinearGroup {i // p i} K ≃* SpecialLinearGroup (Fin 2) K := reindexSL e
  have := sl2_isSimpleGroup (K := K) h4
  exact (e₂.symm.trans e₁).symm.isSimpleGroup

theorem isSimpleGroup_pairBlock [CharP K 2] (h4 : 4 ≤ Nat.card K) {s : Finset (Fin 4)}
    (hs : s.card = 2) : IsSimpleGroup ↥(pairBlock K s) :=
  isSimpleGroup_range_extHom1 (fun k => k ∈ s) h4 (by rw [Fintype.card_subtype]; simpa using hs)

theorem eq_bot_or_eq_of_normal_subgroupOf {Γ : Type*} [Group Γ] (B : Subgroup Γ) [IsSimpleGroup ↥B]
    (N : Subgroup Γ) (hN : N ≤ B) (hnorm : (N.subgroupOf B).Normal) : N = ⊥ ∨ N = B := by
  have : (N.subgroupOf B).Normal := hnorm
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (N.subgroupOf B) with h | h
  · left
    have := congrArg (Subgroup.map B.subtype) h
    rwa [Subgroup.map_subgroupOf_eq_of_le hN, Subgroup.map_bot] at this
  · right
    have := congrArg (Subgroup.map B.subtype) h
    rwa [Subgroup.map_subgroupOf_eq_of_le hN, ← MonoidHom.range_eq_map, Subgroup.range_subtype] at this

end CFSG.RankThree.PartOne.KFCL.L4
