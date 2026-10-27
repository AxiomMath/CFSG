module

public import CFSG.HardMathSupport.Cooperstein.Coordinator.FFSporadic.Co1RankCheck
import Certificates.Kernel.SporSch.Co1Rank.Main
public import CFSG.Sporadic.Co1Block.XFixBase

public section

namespace Certificates

open CFSG.HardMathSupport.Cooperstein.Coordinator.FFSporadic CFSG.Sporadic.Co1Schreier
  CFSG.Sporadic.Co1Block in
theorem certificate129072 :
    Nat.card (Subgroup.closure
        ((fun g => (dagG [A₁, A₂] rankBD).getD (rankBIdx.getD g 0) 1) '' {g | g < 6})) = 2 ^ 15 ∧
      (∀ g < 6, (dagG [A₁, A₂] rankBD).getD (rankBIdx.getD g 0) 1 ∈ GA ∧
        (dagG [A₁, A₂] rankBD).getD (rankBIdx.getD g 0) 1 * A₁ =
          A₁ * (dagG [A₁, A₂] rankBD).getD (rankBIdx.getD g 0) 1) ∧
      ∀ B : Subgroup GL24, B ≤ Subgroup.closure
          ((fun g => (dagG [A₁, A₂] rankBD).getD (rankBIdx.getD g 0) 1) '' {g | g < 6}) →
        (∀ x ∈ B, ∀ y ∈ B, x * y = y * x) → (∀ x ∈ B, x * x = 1) → A₁ ∈ B →
        (∀ x ∈ B, x ≠ 1 → (xFix x).ncard ≠ 2280) → Nat.card B ≤ 16 := CFSG.KD.Co1RankGen.rankB

end Certificates
