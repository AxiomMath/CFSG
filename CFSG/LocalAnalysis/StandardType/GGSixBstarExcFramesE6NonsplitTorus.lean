module

public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerSylow
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcVacuous
public import CFSG.LieType.SeitzGeneration.ExcTorusRankE6
public import CFSG.LocalAnalysis.StandardType.GGPRankBoundsExc
public import CFSG.HardMathSupport.Timmesfeld.DefChar.LieOuterE
public import CFSG.HardMathSupport.Timmesfeld.Proving.ExistsOrderPCentralizer
public import CFSG.HardMathSupport.Timmesfeld.Proving.GLAPrimeCoreCentralizer
public import CFSG.LieType.SeitzGeneration.ExcTorusTwE6Four
public import CFSG.LieType.SeitzGeneration.ExcTorusTwE6Three
public import CFSG.LocalAnalysis.ComponentInitial.BlockOvergroupDichotomy
public import CFSG.LocalAnalysis.ComponentInitial.GeneralizedFittingProduct
public import CFSG.LocalAnalysis.GLTheoremB.QuotientTools

public section

namespace CFSG.StandardType

namespace ExcFrames

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.SeitzGeneration CFSG.Open
  CFSG.RankThree.PartOne.KE
open CFSG.HardMathSupport.Timmesfeld.CrossChar (eq_of_three_le_degCount_E6
  rankLE2_E6_of_degCount_eq_two)

section Torus


theorem sylowTorus_adjoint_E6_two (K : Type) [Field K] [Finite K] {p : ℕ} (hp : p.Prime)
    (hp3 : 3 < p) (he : orderOf ((Nat.card K : ℕ) : ZMod p) = 2) :
    SylowTorus (adjointGroup Tag.E6 K) p 4 := by
  have hS : SylowTorus (adjointGroup Tag.E6 K) p ([1, 1, 2, 2, 2, 2].count 2) :=
    PRankBounds.sylowTorus_of_blocks_of_lt 3 (Or.inl ⟨rfl, rfl⟩) K hp hp3
      (IsWeylMatrix.of_word Tag.E6 e6TwoWord) [1, 1, 2, 2, 2, 2] e6Two_charpoly e6Two_pow he
      (by norm_num) (by decide) (by decide) (by decide)
  exact hS

theorem sylowTorus_adjoint_E6_three (K : Type) [Field K] [Finite K] {p : ℕ} (hp : p.Prime)
    (hp3 : 3 < p) (he : orderOf ((Nat.card K : ℕ) : ZMod p) = 3) :
    SylowTorus (adjointGroup Tag.E6 K) p 3 := by
  have hS : SylowTorus (adjointGroup Tag.E6 K) p ([3, 3, 3].count 3) :=
    PRankBounds.sylowTorus_of_blocks_of_lt 3 (Or.inl ⟨rfl, rfl⟩) K hp hp3
      (IsWeylMatrix.of_word Tag.E6 e6ThreeWord) [3, 3, 3] e6Three_charpoly e6Three_pow he
      (by norm_num) (by decide) (by decide) (by decide)
  exact hS

theorem orderOf_eq_two_of_four_le_card_E6 (K : Type) [Field K] [Finite K] {p : ℕ}
    (hp : p.Prime) (hp3 : 3 < p) (hpq : ¬ p ∣ Nat.card K) (h1 : ¬ p ∣ Nat.card K - 1)
    {A : Subgroup (adjointGroup Tag.E6 K)} (hA : IsElemAbelian p A) (hAc : p ^ 4 ≤ Nat.card A) :
    orderOf ((Nat.card K : ℕ) : ZMod p) = 2 := by
  haveI : Finite (adjointGroup Tag.E6 K) := generated_group_finite Tag.E6 K
  have : Fact p.Prime := ⟨hp⟩
  have hq1 : 1 ≤ Nat.card K := Nat.card_pos
  have he0 := orderOf_natCast_ne_zero hp hpq
  have hne1 : orderOf ((Nat.card K : ℕ) : ZMod p) ≠ 1 := fun h => h1 (by
    have hx : ((Nat.card K : ℕ) : ZMod p) = 1 := orderOf_eq_one_iff.mp h
    have : ((Nat.card K - 1 : ℕ) : ZMod p) = 0 := by
      rw [Nat.cast_sub hq1, hx, Nat.cast_one, sub_self]
    exact (ZMod.natCast_eq_zero_iff _ _).mp this)
  by_contra hne2
  have h3 : 3 ≤ orderOf ((Nat.card K : ℕ) : ZMod p) := by omega
  have hp1 : p ^ 1 < p ^ 4 := Nat.pow_lt_pow_right hp.one_lt (by norm_num)
  have hp2 : p ^ 2 < p ^ 4 := Nat.pow_lt_pow_right hp.one_lt (by norm_num)
  have hp3' : p ^ 3 < p ^ 4 := Nat.pow_lt_pow_right hp.one_lt (by norm_num)
  by_cases hc : 3 ≤ degCount Tag.E6 (orderOf ((Nat.card K : ℕ) : ZMod p))
  · have he3 : orderOf ((Nat.card K : ℕ) : ZMod p) = 3 := by
      have := eq_of_three_le_degCount_E6 hc
      omega
    have hle := (sylowTorus_adjoint_E6_three K hp hp3 he3).rank_le hp hA
    omega
  · by_cases h1c : degCount Tag.E6 (orderOf ((Nat.card K : ℕ) : ZMod p)) ≤ 1
    · have hle := rankLE1_E6 K hp hpq h1c A hA
      rw [pow_one] at hp1
      omega
    · have h2c : degCount Tag.E6 (orderOf ((Nat.card K : ℕ) : ZMod p)) = 2 := by omega
      have hle := rankLE2_E6_of_degCount_eq_two K hp h2c A hA
      omega

theorem sylowTorus_E6_nonsplit_of_four_le_card (K : Type) [Field K] [Finite K] {p : ℕ}
    (hp : p.Prime) (hp3 : 3 < p) (hpq : ¬ p ∣ Nat.card K) (h1 : ¬ p ∣ Nat.card K - 1)
    {A : Subgroup (adjointGroup Tag.E6 K)} (hA : IsElemAbelian p A)
    (hAc : p ^ 4 ≤ Nat.card A) (K₀ : Type) [Field K₀] [Finite K₀]
    (hres : ((Nat.card K₀ : ℕ) : ZMod p) = ((Nat.card K : ℕ) : ZMod p)) :
    SylowTorus (adjointGroup Tag.E6 K₀) p 4 := by
  have he := orderOf_eq_two_of_four_le_card_E6 K hp hp3 hpq h1 hA hAc
  refine sylowTorus_adjoint_E6_two K₀ hp hp3 ?_
  rw [hres]
  exact he

end Torus

end ExcFrames

end CFSG.StandardType
