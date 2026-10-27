module

public import CFSG.LocalAnalysis.UniqueFourCatalog.OddOrthogonalAbstract
public import CFSG.LocalAnalysis.UniqueFourCatalog.Standing4Basic
public import CFSG.ClassicalGroups.Orthogonal.Simple

open CFSG.Open
open CFSG.Yardstones.Mf4cdcdf2e013 (Standing4)

public section

namespace CFSG.LocalAnalysis.UniqueFourCatalog

section OrthModels

open CFSG.Assembly.LowTwoRank CFSG.ClassicalGroups.Orthogonal QuadraticMap
  CFSG.LieType.Universal.Spin
open CFSG.RankThree.PartTwo.Census (isCharTwoType_of_mulEquiv)

variable {K : Type} [Field K] [Finite K]

theorem not_isCharTwoType_statedPOmegaOdd (hodd : Odd (Nat.card K)) {n : ℕ} (hn : 3 ≤ n) :
    ¬ IsCharTwoType (StatedProj (StatedOmega (StatedQuadOdd n K))) := by
  have h2 : (2 : K) ≠ 0 := CFSG.Semidihedral.OddFieldSL2.two_ne_zero_of_odd_card K hodd
  intro h
  refine not_isCharTwoType_projElementary hodd (nondegenerate_polarBilin_quadOdd n K h2)
    (P := oddPair K ⟨0, by omega⟩) (P' := oddPair K ⟨1, by omega⟩)
    (oddPair_orth (by simp [Fin.ext_iff])) ?_
    (isCharTwoType_of_mulEquiv
      (statedProjEquiv (coe_quadOdd n K) (commutator_orthogonalGroup_quadOdd h2 hn)) h)
  rw [Module.finrank_fintype_fun_eq_card]
  simp only [Fintype.card_sum, Fintype.card_fin, Fintype.card_unit]
  omega

theorem not_isCharTwoType_statedPOmegaPlus (hodd : Odd (Nat.card K)) {n : ℕ} (hn : 4 ≤ n) :
    ¬ IsCharTwoType (StatedProj (StatedOmega (StatedQuadPlus n K))) := by
  intro h
  refine not_isCharTwoType_projElementary hodd (nondegenerate_polarBilin_quadPlus n K)
    (P := plusPair K ⟨0, by omega⟩) (P' := plusPair K ⟨1, by omega⟩)
    (plusPair_orth (by simp [Fin.ext_iff])) ?_
    (isCharTwoType_of_mulEquiv
      (statedProjEquiv (coe_quadPlus n K) (commutator_orthogonalGroup_quadPlus (by omega))) h)
  rw [Module.finrank_fintype_fun_eq_card]
  simp only [Fintype.card_sum, Fintype.card_fin]
  omega

theorem not_isCharTwoType_statedPOmegaMinus (hodd : Odd (Nat.card K)) {n : ℕ} (hn : 4 ≤ n)
    {b c : K} (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    ¬ IsCharTwoType (StatedProj (StatedOmega (StatedQuadMinus n K b c))) := by
  intro h
  refine not_isCharTwoType_projElementary hodd (nondegenerate_polarBilin_quadMinus_of_finite n K hirr)
    (P := minusPair K b c ⟨0, by omega⟩) (P' := minusPair K b c ⟨1, by omega⟩)
    (minusPair_orth (by simp [Fin.ext_iff])) ?_
    (isCharTwoType_of_mulEquiv
      (statedProjEquiv (coe_quadMinus n K b c) (commutator_orthogonalGroup_quadMinus hn hirr)) h)
  rw [Module.finrank_fintype_fun_eq_card]
  simp only [Fintype.card_sum, Fintype.card_fin]
  omega

end OrthModels

section OrthTag

open CFSG.Assembly.LowTwoRank

variable {G : Type} [Group G] [Finite G]

theorem false_of_statedPOmegaOdd (hS : Standing4 G) {n p f : ℕ}
    (h : StatedClassicalModel G .POmegaOdd n p f) : False := by
  obtain ⟨⟨hpp, hf, hn3, hp2⟩, K, hKf, hKfin, hcard, ⟨e⟩⟩ := h
  have hodd : Odd (Nat.card K) := by rw [hcard]; exact (hpp.odd_of_ne_two hp2).pow
  exact hS.false_of_not_isCharTwoType e (not_isCharTwoType_statedPOmegaOdd hodd hn3)

theorem false_of_statedPOmegaPlus_odd (hS : Standing4 G) {n p f : ℕ} (hp : p ≠ 2)
    (h : StatedClassicalModel G .POmegaPlus n p f) : False := by
  obtain ⟨⟨hpp, hf, hn4⟩, K, hKf, hKfin, hcard, ⟨e⟩⟩ := h
  have hodd : Odd (Nat.card K) := by rw [hcard]; exact (hpp.odd_of_ne_two hp).pow
  exact hS.false_of_not_isCharTwoType e (not_isCharTwoType_statedPOmegaPlus hodd hn4)

theorem false_of_statedPOmegaMinus_odd (hS : Standing4 G) {n p f : ℕ} (hp : p ≠ 2)
    (h : StatedClassicalModel G .POmegaMinus n p f) : False := by
  obtain ⟨⟨hpp, hf, hn4⟩, K, hKf, hKfin, hcard, b, c, hirr, ⟨e⟩⟩ := h
  have hodd : Odd (Nat.card K) := by rw [hcard]; exact (hpp.odd_of_ne_two hp).pow
  exact hS.false_of_not_isCharTwoType e (not_isCharTwoType_statedPOmegaMinus hodd hn4 hirr)

end OrthTag

end CFSG.LocalAnalysis.UniqueFourCatalog
