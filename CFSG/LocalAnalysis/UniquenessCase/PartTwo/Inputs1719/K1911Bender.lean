module

public import CFSG.LocalAnalysis.UniquenessCase.UC22P2214e1
public import CFSG.GH74.Bender
public import CFSG.Timmesfeld.Bridge.Asc72Bender
public import CFSG.GroupTheory.InvertedOddNoTwoSubgroup

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

theorem k1911_eq_bot_of_bender {Y : Type} [Group Y] [Finite Y] {n : ℕ}
    (hY : IsL2 Y n ∨ IsSz Y n ∨ IsU3 Y n) {B : Subgroup Y} (hB : B ≠ ⊥)
    (hBodd : Odd (Nat.card B)) {s : Y} (hs : ∃ k : ℕ, orderOf s = 2 ^ k)
    (hinv : ∀ b ∈ B, s * b * s⁻¹ = b⁻¹) {R : Subgroup Y} (hR : IsPGroup 2 R)
    (hBR : B ≤ normalizer (R : Set Y)) (hsR : s ∈ normalizer (R : Set Y)) : R = ⊥ := by
  have hK : CFSG.BenderSuzuki.IsBenderGroup Y := by
    rcases hY with hL2 | hSz | hU3
    · exact CFSG.GH74.isBenderGroup_of_fusionIsBenderGroup (uc22p2214_bor_bender_L2 hL2)
    · exact CFSG.GH74.isBenderGroup_of_fusionIsBenderGroup (uc22p2214_bor_bender_Sz hSz)
    · exact CFSG.GH74.isBenderGroup_of_fusionIsBenderGroup (uc22p2214_bor_bender_U3 hU3)
  exact CFSG.GroupTheory.eq_bot_of_isStronglyEmbeddedOrder
    (fun S => CFSG.Timmesfeld.Bridge.Asc72.IsBenderGroup.isStronglyEmbeddedOrder_normalizer hK S)
    hB hBodd hs hinv hR hBR hsR

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

end
