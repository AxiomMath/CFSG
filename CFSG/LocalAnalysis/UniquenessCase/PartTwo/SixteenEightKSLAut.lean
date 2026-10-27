module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenKJPrimeLie
public import CFSG.GroupTheory.PRankBound
public import CFSG.Adapters.StatedClassicalOrders
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.ComponentInitial.LinearModelOuterTwoPart
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.Quasithin.EmptyFaithful.T1515C4Mod
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner)

private theorem s16k_card_mulAut_dvd_of_outer_dvd {X : Type} [Group X] [Finite X] {k : ℕ}
    (hk : Nat.card (Outer X) ∣ k) : Nat.card (MulAut X) ∣ k * Nat.card X := by
  haveI : Finite (MulAut X) :=
    Finite.of_injective (fun φ : MulAut X => (φ : X → X)) DFunLike.coe_injective
  have hinner : Nat.card (inner X) ∣ Nat.card X := by
    have h1 : Nat.card (inner X) = Nat.card (X ⧸ (MulAut.conj : X →* MulAut X).ker) :=
      (Nat.card_congr
        (QuotientGroup.quotientKerEquivRange (MulAut.conj : X →* MulAut X)).toEquiv).symm
    rw [h1]
    exact Subgroup.card_quotient_dvd_card _
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (inner X)]
  exact mul_dvd_mul hk hinner

private theorem s16k_not_pow_dvd (N r : ℕ) (hr : 0 < r) (S T : Finset ℕ) (hN : N ≠ 0)
    (hS : N.primeFactors = S) (hS' : ∀ q ∈ S, q ∉ T → ¬ q ^ r ∣ N) :
    ∀ p : ℕ, p.Prime → p ∉ T → ¬ p ^ r ∣ N := by
  intro p hp hpT h
  have hmem : p ∈ S := by
    rw [← hS]
    exact Nat.mem_primeFactors.2 ⟨hp, (dvd_pow_self p (by omega)).trans h, hN⟩
  exact hS' p hmem hpT h

theorem s16k_pRank_aut_sl_small {X : Type} [Group X] [Finite X] {n : ℕ} (hn : n = 6 ∨ n = 7)
    (hX : IsSLn X n 1) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hp3 : p ≠ 3) :
    CFSG.Open.pRank p (⊤ : Subgroup (MulAut X)) ≤ 2 := by
  have hn3 : 3 ≤ n := by rcases hn with rfl | rfl <;> norm_num
  have hS : CFSG.Open.StatedClassicalModel X .PSL n 2 1 := by
    obtain ⟨K, hF, hfin, hcard, ⟨e⟩⟩ := hX
    letI : Field K := hF
    have hK2 : Nat.card K = 2 := by simpa using hcard
    obtain ⟨f⟩ := s15k_jp_projEquiv hK2 (StatedSL n K)
    exact ⟨⟨Nat.prime_two, le_rfl, by omega,
        fun hc => absurd (congrArg Prod.fst hc) (by omega),
        fun hc => absurd (congrArg Prod.fst hc) (by omega)⟩,
      K, hF, hfin, hcard, ⟨e.trans f.symm⟩⟩
  have hout : Nat.card (Outer X) ∣ 2 := by
    have h := (CFSG.LocalAnalysis.ComponentInitial.linear_model_outer_two_part_bound
      X n 2 1 hS).2.2.2.2 hn3
    simpa using h
  have hcard : Nat.card (MulAut X) ∣ 2 * Nat.card X :=
    s16k_card_mulAut_dvd_of_outer_dvd (X := X) hout
  refine CFSG.GroupTheory.pRank_le_of_not_dvd_pow_succ (H := ⊤) hp ?_
  rw [Subgroup.card_top]
  intro hd
  have hd' : p ^ 3 ∣ 2 * Nat.card X := hd.trans hcard
  rcases hn with rfl | rfl
  · have hcardX : Nat.card X = 20158709760 := by
      rw [CFSG.Open.StatedAPI.card_of_statedClassicalModel_psl (by norm_num) hS]
      decide
    rw [hcardX] at hd'
    exact s16k_not_pow_dvd (2 * 20158709760) 3 (by norm_num) {2, 3, 5, 7, 31} {2, 3}
      (by norm_num) (by simp [Nat.primeFactors])
      (by
        intro q hq hqT
        simp only [Finset.mem_insert, Finset.mem_singleton] at hq
        rcases hq with rfl | rfl | rfl | rfl | rfl
        · exact absurd (by decide : (2 : ℕ) ∈ ({2, 3} : Finset ℕ)) hqT
        · exact absurd (by decide : (3 : ℕ) ∈ ({2, 3} : Finset ℕ)) hqT
        · norm_num
        · norm_num
        · norm_num)
      p hp (by simp only [Finset.mem_insert, Finset.mem_singleton, not_or]; exact ⟨hp2, hp3⟩)
      hd'
  · have hcardX : Nat.card X = 163849992929280 := by
      rw [CFSG.Open.StatedAPI.card_of_statedClassicalModel_psl (by norm_num) hS]
      decide
    rw [hcardX] at hd'
    exact s16k_not_pow_dvd (2 * 163849992929280) 3 (by norm_num) {2, 3, 5, 7, 31, 127} {2, 3}
      (by norm_num) (by simp [Nat.primeFactors])
      (by
        intro q hq hqT
        simp only [Finset.mem_insert, Finset.mem_singleton] at hq
        rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
        · exact absurd (by decide : (2 : ℕ) ∈ ({2, 3} : Finset ℕ)) hqT
        · exact absurd (by decide : (3 : ℕ) ∈ ({2, 3} : Finset ℕ)) hqT
        · norm_num
        · norm_num
        · norm_num
        · norm_num)
      p hp (by simp only [Finset.mem_insert, Finset.mem_singleton, not_or]; exact ⟨hp2, hp3⟩)
      hd'

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
