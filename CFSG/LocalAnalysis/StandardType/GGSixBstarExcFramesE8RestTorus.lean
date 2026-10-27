module

public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerSylow
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcVacuous
public import CFSG.LieType.SeitzGeneration.ExcTorusRankE8
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
open CFSG.HardMathSupport.Timmesfeld.CrossChar (sylowTorus_of_blocks_of_three_lt not_dvd_of_blocks
  not_dvd_div_of_720 eq_of_three_le_degCount_E8 rankLE2_E8_of_degCount_eq_two)

section Torus


theorem sylowTorus_adjoint_E8_four (K : Type) [Field K] [Finite K] {p : ℕ} (hp : p.Prime)
    (h7 : 7 ≤ p) (hpq : ¬ p ∣ Nat.card K)
    (he : orderOf ((Nat.card K : ℕ) : ZMod p) = 3 ∨ orderOf ((Nat.card K : ℕ) : ZMod p) = 4 ∨
      orderOf ((Nat.card K : ℕ) : ZMod p) = 6) :
    SylowTorus (adjointGroup Tag.E8 K) p 4 := by
  have hp3 : 3 < p := by omega
  rcases he with he | he | he
  · have hS : SylowTorus (adjointGroup Tag.E8 K) p ([3, 3, 3, 3].count 3) :=
      sylowTorus_of_blocks_of_three_lt 1 (Or.inr (Or.inr ⟨rfl, rfl⟩)) K hp hp3 hpq
        (IsWeylMatrix.of_word Tag.E8 e8ThreeWord) [3, 3, 3, 3] e8Three_charpoly e8Three_pow he
        (not_dvd_of_blocks hp h7 (by decide)) (not_dvd_div_of_720 hp h7 (by decide))
        (by decide)
    exact hS
  · have hS : SylowTorus (adjointGroup Tag.E8 K) p ([4, 4, 4, 4].count 4) :=
      sylowTorus_of_blocks_of_three_lt 1 (Or.inr (Or.inr ⟨rfl, rfl⟩)) K hp hp3 hpq
        (IsWeylMatrix.of_word Tag.E8 e8FourWord) [4, 4, 4, 4] e8Four_charpoly e8Four_pow he
        (not_dvd_of_blocks hp h7 (by decide)) (not_dvd_div_of_720 hp h7 (by decide))
        (by decide)
    exact hS
  · have hS : SylowTorus (adjointGroup Tag.E8 K) p ([6, 6, 6, 6].count 6) :=
      sylowTorus_of_blocks_of_three_lt 1 (Or.inr (Or.inr ⟨rfl, rfl⟩)) K hp hp3 hpq
        (IsWeylMatrix.of_word Tag.E8 e8SixWord) [6, 6, 6, 6] e8Six_charpoly e8Six_pow he
        (not_dvd_of_blocks hp h7 (by decide)) (not_dvd_div_of_720 hp h7 (by decide))
        (by decide)
    exact hS

theorem orderOf_mem_of_four_le_card (K : Type) [Field K] [Finite K] {p : ℕ} (hp : p.Prime)
    (hpq : ¬ p ∣ Nat.card K) (h1 : ¬ p ∣ Nat.card K - 1) (h2 : ¬ p ∣ Nat.card K + 1)
    {A : Subgroup (adjointGroup Tag.E8 K)} (hA : IsElemAbelian p A) (hAc : p ^ 4 ≤ Nat.card A) :
    orderOf ((Nat.card K : ℕ) : ZMod p) = 3 ∨ orderOf ((Nat.card K : ℕ) : ZMod p) = 4 ∨
      orderOf ((Nat.card K : ℕ) : ZMod p) = 6 := by
  haveI : Finite (adjointGroup Tag.E8 K) := generated_group_finite Tag.E8 K
  have hq1 : 1 ≤ Nat.card K := Nat.card_pos
  have h3 : 3 ≤ orderOf ((Nat.card K : ℕ) : ZMod p) :=
    PRankBounds.three_le_orderOf hp hpq hq1 h1 h2
  have hp1 : p ^ 1 < p ^ 4 := Nat.pow_lt_pow_right hp.one_lt (by norm_num)
  have hp2 : p ^ 2 < p ^ 4 := Nat.pow_lt_pow_right hp.one_lt (by norm_num)
  by_cases hc : 3 ≤ degCount Tag.E8 (orderOf ((Nat.card K : ℕ) : ZMod p))
  · have := eq_of_three_le_degCount_E8 hc
    omega
  · exfalso
    by_cases h1c : degCount Tag.E8 (orderOf ((Nat.card K : ℕ) : ZMod p)) ≤ 1
    · have hle := rankLE1_E8 K hp hpq h1c A hA
      rw [pow_one] at hp1
      omega
    · have h2c : degCount Tag.E8 (orderOf ((Nat.card K : ℕ) : ZMod p)) = 2 := by omega
      have hle := rankLE2_E8_of_degCount_eq_two K hp h2c A hA
      omega

theorem sylowTorus_E8_rest_of_four_le_card (K : Type) [Field K] [Finite K] {p : ℕ}
    (hp : p.Prime) (h7 : 7 ≤ p) (hpq : ¬ p ∣ Nat.card K) (h1 : ¬ p ∣ Nat.card K - 1)
    (h2 : ¬ p ∣ Nat.card K + 1) {A : Subgroup (adjointGroup Tag.E8 K)} (hA : IsElemAbelian p A)
    (hAc : p ^ 4 ≤ Nat.card A) (K₀ : Type) [Field K₀] [Finite K₀]
    (hres : ((Nat.card K₀ : ℕ) : ZMod p) = ((Nat.card K : ℕ) : ZMod p)) :
    SylowTorus (adjointGroup Tag.E8 K₀) p 4 := by
  have he := orderOf_mem_of_four_le_card K hp hpq h1 h2 hA hAc
  have hpq₀ : ¬ p ∣ Nat.card K₀ := by
    intro hd
    apply hpq
    have : Fact p.Prime := ⟨hp⟩
    have h0 : ((Nat.card K₀ : ℕ) : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff _ _).2 hd
    rw [hres] at h0
    exact (ZMod.natCast_eq_zero_iff _ _).1 h0
  refine sylowTorus_adjoint_E8_four K₀ hp h7 hpq₀ ?_
  rw [hres]
  exact he

end Torus

end ExcFrames

end CFSG.StandardType
