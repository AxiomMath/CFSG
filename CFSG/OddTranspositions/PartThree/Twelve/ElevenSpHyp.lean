module

public import CFSG.OddTranspositions.PartThree.Twelve.SpChart
public import CFSG.OddTranspositions.PartThree.Twelve.Minimal

public section

namespace CFSG.OddTranspositions.PartThree.ElevenSp

open CFSG.Timmesfeld.Bridge CFSG.Timmesfeld.Bridge.Asc72 CFSG.OddTranspositions.PartFour
open CFSG.LocalAnalysis.WeakClosure81.SevenK

variable {G : Type} [Group G] [Finite G] {D : Set G}

structure SpBranch (hC : HypothesisC D) : Type where
  hIH : Theorem4Below (Nat.card G)
  hrad : ∀ N : Subgroup G, N.Normal → Group.IsSolvable N → N = ⊥
  hMZ : CFSG.solvableRadical (Halpha D hC.alpha) ≤ Subgroup.center (Halpha D hC.alpha)
  hα : hC.alpha = {hC.d}
  s : Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha)
  hs : s ∈ imageClass hC
  n : ℕ
  f : ℕ
  hn : 4 ≤ n
  hf : 2 ≤ f
  hSp : IsSymplecticTransvection
    (Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha)) n f s
  hdiam : ∀ a ∈ D, ∀ b ∈ D, ¬ Commute a b → (commSet D a ∩ commSet D b).Nonempty

namespace SpBranch

variable {hC : HypothesisC D} (B : SpBranch hC)

omit [Finite G] in
theorem four_le_two_pow : 4 ≤ 2 ^ B.f :=
  le_trans (by norm_num) (Nat.pow_le_pow_right (by norm_num) B.hf)

omit [Finite G] in
theorem two_lt_card {F : Type*} (hF : Nat.card F = 2 ^ B.f) : 2 < Nat.card F := by
  rw [hF]
  exact lt_of_lt_of_le (by norm_num) B.four_le_two_pow

omit [Finite G] in
theorem two_le_rank {k : ℕ} (hnk : B.n = 2 * k) : 2 ≤ k := by
  have hn := B.hn
  rw [hnk] at hn
  omega

end SpBranch

end CFSG.OddTranspositions.PartThree.ElevenSp

end
