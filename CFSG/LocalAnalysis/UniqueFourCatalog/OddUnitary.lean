module

public import CFSG.LocalAnalysis.UniqueFourCatalog.OddClassicalGeneric
public import CFSG.Yardstones.Mf4cdcdf2e013.Definitions
public import CFSG.LocalAnalysis.UniqueFourCatalog.Standing4Basic
public import CFSG.LocalAnalysis.RankThreeUC.CatalogClosureOddLie
public import CFSG.RankThree.PartTwo.Census.OddClassical.UnitaryComponent
public import CFSG.RankThree.PartTwo.Census.OddClassical.LinearComponent
public import CFSG.RankThree.PartTwo.Census.OddClassical.SmallThree
public import CFSG.RankThree.PartTwo.Census.OddClassical.UnitaryFourThree
public import CFSG.RankThree.PartOne.SLB4B.ModelU
public import CFSG.RankThree.PartOne.SLB4B.RankFourU
public import CFSG.LieType.Universal.Unitary.Clause0
public import CFSG.ClassicalGroups.UnitaryFlag.GroupData
public import CFSG.Adapters.ClassicalCatalogReverse
public import CFSG.LocalAnalysis.SectionRank.ClassicalOdd.Basic
public import CFSG.CGT.Timmesfeld75.Statements
public import CFSG.Foundations
public import CFSG.LieType.Steinberg.CentralExt.PSL2Multiplier
public import CFSG.LocalAnalysis.ComponentInitial.LayerComponentOrbit
public import CFSG.LocalAnalysis.SectionRank.Ccomm.Supercritical
public import CFSG.Mathlib.LinearAlgebra.BilinForm.Determinant
public import CFSG.Quasithin.Background.A1bGroups
public import CFSG.RankThree.PartOne.N143.LowTwoRankSplit
public import CFSG.RankThree.PartOne.N143.SectionCenter
public import CFSG.RankThree.PartOne.N143.SectionRankBound
public import CFSG.RankThree.PartOne.N143.SectionRankProof
public import CFSG.RankThree.PartOne.N143.SectionRankSplit
public import CFSG.RankThree.PartOne.N143.SectionReduce
public import CFSG.RankThree.PartOne.S9.Sylow.GlobalLemmas
public import CFSG.RankThree.PartOne.S9.Sylow.GlobalRelative
public import CFSG.RankThree.PartOne.S9.Sylow.ResidualLocal
public import CFSG.RankThree.SubgroupLists.UnitaryThreeFamily

open CFSG.Open
open CFSG.Yardstones.Mf4cdcdf2e013 (Standing4)

public section

namespace CFSG.LocalAnalysis.UniqueFourCatalog

section PSUBlock

open Matrix CFSG.RankThree.PartOne.SLB4B CFSG.RankThree.PartTwo.Census
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.Assembly.LowTwoRank CFSG.ClassicalGroups.UnitaryFlag
open scoped MatrixGroups

variable {p f : ℕ} {K : Type} [Field K] {m : ℕ}

theorem conj_mem_range_suBlock (h : UnitaryFieldData p f K) (h2 : (2 : K) ≠ 0)
    (hq : 1 ≤ p ^ f) (hq' : Odd (p ^ f)) {g : StatedSU (4 + m) (p ^ f) K}
    (hg : g * suSign hq' = suSign hq' * g) (X : StatedSU 4 (p ^ f) K) :
    g * suBlock hq X * g⁻¹ ∈ (suBlock (K := K) (m := m) hq).range := by
  have hcomm : ∀ x : StatedSU (4 + m) (p ^ f) K, x * suSign hq' = suSign hq' * x →
      ∃ A D, ((x : GL (Fin (4 + m)) K) : Matrix (Fin (4 + m)) (Fin (4 + m)) K) =
        diagBlock A D := fun x hx =>
    eq_diagBlock_of_comm h2 (by
      have := congrArg (fun y : StatedSU (4 + m) (p ^ f) K => ((y : GL (Fin (4 + m)) K) :
        Matrix (Fin (4 + m)) (Fin (4 + m)) K)) hx
      simp only [Subgroup.coe_mul, Units.val_mul, suSign, coe_signGL] at this
      exact this)
  have hg' : g⁻¹ * suSign hq' = suSign hq' * g⁻¹ := (Commute.inv_left hg).eq
  obtain ⟨A, D, hAD⟩ := hcomm g hg
  obtain ⟨A', D', hAD'⟩ := hcomm g⁻¹ hg'
  have hone : diagBlock (A * A') (D * D') = diagBlock 1 1 := by
    rw [← diagBlock_mul, ← hAD, ← hAD', diagBlock_one, ← Units.val_mul, ← Subgroup.coe_mul,
      mul_inv_cancel, Subgroup.coe_one, Units.val_one]
  obtain ⟨hA, hD⟩ := diagBlock_injective hone
  have hunit : ∀ x : StatedSU (4 + m) (p ^ f) K, ∀ A D, ((x : GL (Fin (4 + m)) K) :
      Matrix (Fin (4 + m)) (Fin (4 + m)) K) = diagBlock A D → (A.map h.bar)ᵀ * A = 1 := by
    intro x A D hx
    have hx2 := ((mem_unitarySU_iff h).mp x.2).2
    rw [hx, diagBlock_map, diagBlock_transpose, diagBlock_mul, ← diagBlock_one] at hx2
    exact (diagBlock_injective hx2).1
  have hAu := hunit g A D hAD
  have hA'u := hunit g⁻¹ A' D' hAD'
  set Xm := ((X : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K)
  obtain ⟨hXdet, hXu⟩ := (mem_unitarySU_iff h).mp X.2
  have hdet : (A * Xm * A').det = 1 := by
    rw [det_mul, det_mul, hXdet, mul_one, ← det_mul, hA, det_one]
  set Y : GL (Fin 4) K :=
    GeneralLinearGroup.mkOfDetNeZero (A * Xm * A') (by rw [hdet]; exact one_ne_zero)
  have hYcoe : (Y : Matrix (Fin 4) (Fin 4) K) = A * Xm * A' := rfl
  have hY : Y ∈ StatedSU 4 (p ^ f) K := by
    rw [show StatedSU 4 (p ^ f) K = unitarySU p f K 4 from rfl, mem_unitarySU_iff h, hYcoe]
    refine ⟨hdet, ?_⟩
    rw [Matrix.map_mul, Matrix.map_mul, transpose_mul, transpose_mul]
    calc (A'.map h.bar)ᵀ * ((Xm.map h.bar)ᵀ * (A.map h.bar)ᵀ) * (A * Xm * A')
        = (A'.map h.bar)ᵀ * ((Xm.map h.bar)ᵀ * ((A.map h.bar)ᵀ * A) * Xm) * A' := by
          simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hAu, Matrix.mul_one, hXu, Matrix.mul_one, hA'u]
  refine ⟨⟨Y, hY⟩, Subtype.ext (Units.ext ?_)⟩
  rw [coe_suBlock]
  change diagBlock (A * Xm * A') 1 = ((g : GL (Fin (4 + m)) K) :
      Matrix (Fin (4 + m)) (Fin (4 + m)) K) * diagBlock Xm 1 *
    (((g⁻¹ : StatedSU (4 + m) (p ^ f) K) : GL (Fin (4 + m)) K) :
      Matrix (Fin (4 + m)) (Fin (4 + m)) K)
  rw [hAD, hAD', diagBlock_mul, diagBlock_mul, Matrix.mul_one, hD]

theorem suBlock_injective (hq : 1 ≤ p ^ f) (hm : 1 ≤ m) :
    Function.Injective (suBlock (K := K) (m := m) hq) := by
  have h := psuEmb_injective (K := K) (m := m) hq hm
  rw [psuEmb, MonoidHom.coe_comp] at h
  exact Function.Injective.of_comp h

theorem not_isCharTwoType_PSU_block_four [Fact p.Prime] [Finite K]
    (hK : Nat.card K = (p ^ f) ^ 2) (hp2 : p ≠ 2) (hf : 1 ≤ f) (hm : 1 ≤ m) :
    ¬ IsCharTwoType (StatedProj (StatedSU (4 + m) (p ^ f) K)) := by
  have h : UnitaryFieldData p f K := ⟨Fact.out, hf, by rw [hK, ← pow_mul, mul_comm]⟩
  have h2 : (2 : K) ≠ 0 := two_ne_zero_of_unitaryFieldData h hp2
  have hq : 1 ≤ p ^ f := Nat.one_le_pow _ _ (Fact.out : p.Prime).pos
  have hq' : Odd (p ^ f) := ((Fact.out : p.Prime).odd_of_ne_two hp2).pow
  have hneg : (-1 : K) ≠ 1 := fun h1 => h2 (by linear_combination -h1)
  have hqs : CFSG.Open.IsQuasisimple ↥(suBlock (K := K) (m := m) hq).range := by
    have hq4 := (CFSG.LieType.Universal.Unitary.isQuasisimple_statedSU_of_card hK (n := 4)
      (by norm_num) (fun h1 => by simp at h1)).1
    exact CFSG.Open.IsQuasisimple.of_mulEquiv
      (MonoidHom.ofInjective (suBlock_injective hq hm)).symm ⟨hq4.1.commutator_eq_top, hq4.2.1⟩
  refine not_isCharTwoType_quotient_of_quasisimple (H := StatedSU (4 + m) (p ^ f) K)
    ((StatedScalars (Fin (4 + m)) K).subgroupOf _)
    (CFSG.Open.StatedAPI.statedScalars_subgroupOf_le_center _) (t := suSign hq')
    ?_ ?_ (J := (suBlock (K := K) (m := m) hq).range) ?_ ?_ ?_ hqs
  · intro ht
    exact signGL_not_scalar hm hneg (Subgroup.mem_subgroupOf.mp ht)
  · rw [show (suSign (K := K) (m := m) hq') ^ 2 = 1 from Subtype.ext signGL_sq]
    exact Subgroup.one_mem _
  · rintro _ ⟨X, rfl⟩
    exact Subtype.ext (blockGL_commute_signGL _)
  · rintro g hg _ ⟨X, rfl⟩
    exact conj_mem_range_suBlock h h2 hq hq' hg X
  · rw [eq_bot_iff]
    rintro _ hx
    obtain ⟨⟨X, rfl⟩, hc⟩ := Subgroup.mem_inf.mp hx
    have h1 : psuEmb (K := K) (m := m) hq X = 1 := by
      rw [psuEmb, MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
      exact hc
    rw [psuEmb_injective hq hm (h1.trans (map_one _).symm), map_one]
    exact Subgroup.one_mem _

end PSUBlock

section PSUTag

open CFSG.Assembly CFSG.Assembly.RankThreeEven CFSG.RankThree.PartTwo.Census
  CFSG.ClassicalGroups.UnitaryFlag CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.RankThreeUC
  (card_PSU_three_three card_PSU_four_three cube_free_6048 cube_free_3265920)

variable {G : Type} [Group G] [Finite G]

theorem false_of_statedPSU_odd (hS : Standing4 G) {n p f : ℕ} (hp : p ≠ 2)
    (h : StatedClassicalModel G .PSU n p f) : False := by
  obtain ⟨⟨hpp, hf, hn3, hn32⟩, K, hKf, hKfin, hcard, ⟨e⟩⟩ := h
  have : Fact p.Prime := ⟨hpp⟩
  have hqodd : Odd (p ^ f) := (hpp.odd_of_ne_two hp).pow
  by_cases hq3 : p ^ f = 3
  · obtain ⟨rfl, rfl⟩ := CFSG.ClassicalModels.eq_three_one_of_pow_eq_three hpp hf hq3
    have hK9 : Nat.card K = 9 := by rw [hcard]; norm_num
    have : CharP K 3 :=
      CFSG.SectionRank.ClassicalOdd.charP_of_card (f := 2) (by rw [hK9]; norm_num)
    rcases (show n = 3 ∨ n = 4 ∨ 5 ≤ n by omega) with rfl | rfl | h5
    · have e3 : G ≃* StatedProj (StatedSU 3 3 K) := e
      refine hS.false_of_card e3 (N := 6048) {3} (card_PSU_three_three hK9) ?_ cube_free_6048
      intro _ r hr _ _
      obtain rfl : r = 3 := by simpa using hr
      exact localRank_three_PSU_three_le hK9
    · have e3 : G ≃* StatedProj (StatedSU 4 3 K) := e
      refine hS.false_of_card e3 (N := 3265920) {3} (card_PSU_four_three hK9) ?_
        cube_free_3265920
      intro _ r hr _ _
      obtain rfl : r = 3 := by simpa using hr
      exact localRankThreeU43 _ hK9
    · obtain ⟨m, rfl⟩ : ∃ m, n = 4 + m := ⟨n - 4, by omega⟩
      exact hS.false_of_not_isCharTwoType e
        (not_isCharTwoType_PSU_block_four hcard hp hf (by omega))
  · have h5 : 5 ≤ p ^ f := by
      have h1 : 1 < p ^ f := Nat.one_lt_pow (by omega) hpp.one_lt
      obtain ⟨k, hk⟩ := hqodd
      omega
    have hU : UnitaryFieldData p f K := ⟨hpp, hf, by rw [hcard, ← pow_mul, mul_comm]⟩
    obtain ⟨m, rfl⟩ : ∃ m, n = 2 + m := ⟨n - 2, by omega⟩
    exact hS.false_of_not_isCharTwoType (e.trans (unitaryPSUEquiv hU (by omega)).symm)
      (not_isCharTwoType_unitaryPSU_block hU hp h5 (by omega))

end PSUTag

end CFSG.LocalAnalysis.UniqueFourCatalog
