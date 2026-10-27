module

public import CFSG.LocalAnalysis.StandardType.GGTwAutDefs
public import CFSG.LocalAnalysis.StandardType.GGTableBOrthRestEndRankMinus
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongOFRCOrthMinus
public import CFSG.LieType.SeitzGeneration.StandardTypeOrthModel
public import CFSG.HardMathSupport.Timmesfeld.LinearRank.ProjRank
public import CFSG.LocalAnalysis.SectionRank.PRank
public import CFSG.HardMathSupport.Lang.Coordinator.OuterFixedOrderFamilies

public section

namespace CFSG.StandardType

open CFSG.Assembly TableB

private theorem twomle_natCard_cast_eq_one {K : Type} (hpos : 1 ≤ Nat.card K)
    (h3 : 3 ∣ Nat.card K - 1) : ((Nat.card K : ℕ) : ZMod 3) = 1 := by
  have h1 : ((Nat.card K - 1 : ℕ) : ZMod 3) = 0 :=
    (ZMod.natCast_eq_zero_iff (Nat.card K - 1) 3).mpr h3
  have hsplit : Nat.card K = (Nat.card K - 1) + 1 := (Nat.succ_pred_eq_of_pos hpos).symm
  rw [hsplit, Nat.cast_add, Nat.cast_one, h1, zero_add]

private theorem twomle_orderOf_natCard_eq_one {K : Type} (hpos : 1 ≤ Nat.card K)
    (h3 : 3 ∣ Nat.card K - 1) : orderOf ((Nat.card K : ℕ) : ZMod 3) = 1 :=
  orderOf_eq_one_iff.mpr (twomle_natCard_cast_eq_one hpos h3)

private theorem twomle_three_dvd_pow_sub_one {K : Type} (hpos : 1 ≤ Nat.card K) (N : ℕ)
    (h3 : 3 ∣ Nat.card K - 1) : ((3 : ℕ) : ℤ) ∣ (Nat.card K : ℤ) ^ N + (-1) := by
  have hcast : ((Nat.card K : ℕ) : ZMod 3) = 1 := twomle_natCard_cast_eq_one hpos h3
  refine (ZMod.intCast_zmod_eq_zero_iff_dvd ((Nat.card K : ℤ) ^ N + (-1)) 3).mp ?_
  push_cast
  rw [hcast]
  ring

theorem ggTwOm_rankLE_rec {K : Type} [Field K] [Finite K] [CharP K 2] {n m r : ℕ} {b c : K}
    (hK : Nat.card K = 2 ^ n) (hbc : ∀ s : K, s ^ 2 + b * s + c ≠ 0) (hr : 3 ≤ r) (hmr : m = r)
    (h3 : 3 ∣ 2 ^ n - 1 ∨ (Odd r ∧ 3 ∣ 2 ^ n + 1)) :
    GGElemAbelianRankLE (LargeEvenProj (LargeEvenOmega (LargeEvenQMinus m b c))) 3 r := by
  have hm3 : 3 ≤ m := by omega
  have hpos : 1 ≤ Nat.card K := Nat.card_pos
  rcases h3 with h3 | ⟨hodd, hpn⟩
  ·
    have h3K : 3 ∣ Nat.card K - 1 := by rw [hK]; exact h3
    have hnotdvd : ¬ 3 ∣ Nat.card K := by
      rw [hK]
      intro h
      have h32 : 3 ∣ 2 := Nat.prime_three.dvd_of_dvd_pow h
      norm_num at h32
    have hord : orderOf ((Nat.card K : ℕ) : ZMod 3) = 1 :=
      twomle_orderOf_natCard_eq_one hpos h3K
    have hdvd : ((3 : ℕ) : ℤ) ∣ (Nat.card K : ℤ) ^ (m + 1) + (-1) :=
      twomle_three_dvd_pow_sub_one hpos (m + 1) h3K
    have hformula :=
      CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KD291OL.pRank_statedProj_OmegaMinus_formula
        (F := K) (p := 3) (n := m + 1) (b := b) (c := c)
        Nat.prime_three (by norm_num) (by omega) hbc hnotdvd
    have hrankStated :
        CFSG.Open.pRank 3 (⊤ : Subgroup
          (CFSG.Open.StatedProj (CFSG.Open.StatedOmega
            (CFSG.Open.StatedQuadMinus (m + 1) K b c)))) = m := by
      rw [hformula, if_pos hdvd, if_neg (by rw [hord]; decide), hord, Nat.div_one]
      omega
    have heq := CFSG.LieType.SeitzGeneration.standardTypeOmegaMinusEquiv m K b c
    have hrankR : CFSG.Open.pRank 3 (⊤ : Subgroup
        (LargeEvenProj (LargeEvenOmega (LargeEvenQMinus m b c)))) = m := by
      rw [CFSG.SectionRank.pRank_top_eq_of_mulEquiv (by norm_num : 1 < 3) heq]
      exact hrankStated
    intro E hE
    refine CFSG.HardMathSupport.Timmesfeld.LinearRank.card_le_of_pRank_le
      Nat.prime_three ?_ E hE
    rw [hrankR]
    exact le_of_eq hmr
  ·
    have hoddm : Odd m := by rw [hmr]; exact hodd
    intro E hE
    have h := ggOrthRestMinusRankInput_holds K n m 3 b c hK hm3 hoddm
      Nat.prime_three hpn hbc E hE
    exact h.trans (le_of_eq (by rw [hmr]))

end CFSG.StandardType

end
