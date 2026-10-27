module

public import CFSG.RankThree.PartOne.SEITZ5.UTop
public import CFSG.RankThree.PartOne.SEITZ2.SUnTopFull
import all CFSG.RankThree.PartOne.SEITZ2.SUnPair

public section

namespace CFSG.RankThree.PartOne.SEITZ5

open Matrix CFSG.ClassicalGroups.Unitary CFSG.LieType.Universal.Unitary
open CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag
open CFSG.RankThree.PartOne.CTP CFSG.RankThree.Classical
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.LieType.BorelTits (unitaryInvolution unitaryInvolution_apply)
open CFSG.RankThree.PartOne.KFU CFSG.RankThree.PartOne.KCUnitaryCoord
open CFSG.RankThree.PartOne.SEITZ2

theorem subfieldPairSUF2Odd_of_four_le {n : ℕ} (hn : 4 ≤ n) :
    SubfieldPairSUF2Odd n := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  intro f f₀ K _ h k h₀ hbar p hp hp2 hf hf₀ A hne
  have hf₀' : f₀ = 1 := hf₀
  have : Finite K := h.finite
  have : CharP K 2 := h.charP
  have : Finite k := h₀.finite
  have : CharP k 2 := h₀.charP
  have hf2 : 2 ≤ f := by rw [hf, hf₀']; have := hp.two_le; omega
  have hσ : IsUnitaryInvolution (unitaryInvolution K 2 f) :=
    isUnitaryInvolution_unitaryInvolution h.card_eq_sq
  have hσ₀ : IsUnitaryInvolution (unitaryInvolution k 2 f₀) :=
    isUnitaryInvolution_unitaryInvolution h₀.card_eq_sq
  have hq2 : 2 ^ f ≠ 2 := by
    have : 2 ^ 2 ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf2
    omega
  have hk4c : Nat.card k = 4 := by
    have := h₀.card_eq_sq
    rw [hf₀'] at this
    norm_num at this
    exact this
  refine CFSG.RankThree.PartOne.SEITZ2.closure_eq_top_of_involution_pair h h₀ hbar hf A hne
    fun hσk hK hcardk0 ω hωk hω1 hωn A' hA hneG => ?_
  have hr2 : Nat.card (ratFix (unitaryInvolution K 2 f) k) = 2 := by
    rw [hcardk0, hf₀']
    norm_num
  have hfull := exists_hfull (k := k) (N := m + 1) hn hσ.invol hσ₀ hσk hp hp2 hK hr2 hk4c hωk hω1
    hωn A' hA hneG
  exact su_pair_top_of_full hσ hσ₀ hσk hp hp2 hK hωk hω1 hωn h.card_eq_sq hq2 (by omega) A' hA
    hfull

theorem subfieldPairSUF2_of_four_le {n : ℕ} (hn : 4 ≤ n) :
    SubfieldPairSUF2 n :=
  (subfieldPairSUF2Odd_of_four_le hn).subfieldPairSUF2

end CFSG.RankThree.PartOne.SEITZ5
