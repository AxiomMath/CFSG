module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KNotLarge23.Arith
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenDefs
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels
public import CFSG.Timmesfeld.Orders.Classical

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.KNL23

open CFSG.Open CFSG.Timmesfeld.ClassicalOrders
open CFSG.LocalAnalysis.UniquenessCase.PartTwo

theorem card_quotient_eq_index {Q : Type} [Group Q] (N : Subgroup Q) [N.Normal] :
    Nat.card (Q ⧸ N) = N.index := rfl

theorem card_isSp4 {T : Type} [Group T] {n : ℕ} (h : IsSp4 T n) :
    Nat.card T = (2 ^ n) ^ 4 * (((2 ^ n) ^ 2 - 1) * ((2 ^ n) ^ 4 - 1)) := by
  have hc := CFSG.Blueprint.LieModel.statedClassicalModel h (by decide)
  obtain ⟨-, K, hF, hFin, hK, ⟨e⟩⟩ := hc
  let _inst : Field K := hF
  have := hFin
  have := charP_two_of_card_eq hK
  rw [Nat.card_congr e.toEquiv, card_statedProj_statedSp_of_charTwo, hK]
  simp [Finset.prod_Icc_succ_top]


theorem card_isU4 {T : Type} [Group T] {n : ℕ} (hn : 1 ≤ n) (h : IsU4 T n) :
    Nat.card T =
      (2 ^ n) ^ 6 * (((2 ^ n) ^ 2 - 1) * ((2 ^ n) ^ 3 + 1) * ((2 ^ n) ^ 4 - 1)) := by
  have hc := CFSG.Blueprint.LieModel.statedClassicalModel h (by decide)
  obtain ⟨-, K, hF, hFin, hK, ⟨e⟩⟩ := hc
  let _inst : Field K := hF
  rw [Nat.card_congr e.toEquiv, card_statedProj_statedSU Nat.prime_two hn hK (by norm_num)]
  have hodd : Odd (2 ^ n + 1) := (Nat.even_pow.mpr ⟨even_two, by omega⟩).add_one
  have hg : Nat.gcd 4 (2 ^ n + 1) = 1 := by
    have := Nat.Coprime.pow_left 2 (Nat.coprime_two_left.mpr hodd)
    simpa using this
  rw [hg, Nat.div_one]
  simp [Finset.prod_Icc_succ_top]
  have h1 : (((2 ^ n) ^ 2 : ℤ)).toNat = (2 ^ n) ^ 2 := by
    have : (((2 ^ n) ^ 2 : ℤ)) = (((2 ^ n) ^ 2 : ℕ) : ℤ) := by push_cast; rfl
    rw [this, Int.toNat_natCast]
  have h2 : (((2 ^ n) ^ 3 + 1 : ℤ)).toNat = (2 ^ n) ^ 3 + 1 := by
    have : (((2 ^ n) ^ 3 + 1 : ℤ)) = (((2 ^ n) ^ 3 + 1 : ℕ) : ℤ) := by push_cast; rfl
    rw [this, Int.toNat_natCast]
  have h3 : (((2 ^ n) ^ 4 : ℤ)).toNat = (2 ^ n) ^ 4 := by
    have : (((2 ^ n) ^ 4 : ℤ)) = (((2 ^ n) ^ 4 : ℕ) : ℤ) := by push_cast; rfl
    rw [this, Int.toNat_natCast]
  rw [h1, h2, h3]


theorem card_target {T : Type} [Group T] {n : ℕ} (hn : 1 ≤ n)
    (h : IsSLn T 3 n ∨ IsSp4 T n ∨ IsU4 T n) : targetOrder (2 ^ n) (Nat.card T) := by
  rcases h with ⟨K, hF, hFin, hK, ⟨e⟩⟩ | h | h
  · let _inst : Field K := hF
    have := hFin
    left
    rw [Nat.card_congr e.toEquiv, StatedAPI.card_statedSL_three, hK]
  · exact Or.inr (Or.inl (card_isSp4 h))
  · exact Or.inr (Or.inr (card_isU4 hn h))

end CFSG.LocalAnalysis.UniquenessCase.UC22.KNL23

end
