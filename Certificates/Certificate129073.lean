module

public import CFSG.HardMathSupport.Cooperstein.Coordinator.FFSporadic.Co1RankCheck
public import CFSG.Sporadic.Co1Block.Cent
import Certificates.Kernel.SporSch.Co1Rank.Main
public import CFSG.Sporadic.Co1Block.XFixBase

public section

namespace Certificates

open CFSG.HardMathSupport.Cooperstein.Coordinator.FFSporadic CFSG.Sporadic.Co1Schreier
  CFSG.Sporadic.Co1Block in
theorem certificate129073 :
    Nat.card (Subgroup.closure ((fun g => (dagG (brayEltsG (iotaC : GL24) twoCD1 twoCBray)
        rankCD2).getD (rankCIdx.getD g 0) 1) '' {g | g < rankCIdx.length})) = 2 ^ 18 ∧
      (∀ g < rankCIdx.length,
        (dagG (brayEltsG (iotaC : GL24) twoCD1 twoCBray) rankCD2).getD (rankCIdx.getD g 0) 1 ∈ GA ∧
        (dagG (brayEltsG (iotaC : GL24) twoCD1 twoCBray) rankCD2).getD (rankCIdx.getD g 0) 1 *
            (iotaC : GL24) = (iotaC : GL24) *
          (dagG (brayEltsG (iotaC : GL24) twoCD1 twoCBray) rankCD2).getD (rankCIdx.getD g 0) 1) ∧
      ∀ B : Subgroup GL24, B ≤ Subgroup.closure ((fun g => (dagG (brayEltsG (iotaC : GL24)
          twoCD1 twoCBray) rankCD2).getD (rankCIdx.getD g 0) 1) '' {g | g < rankCIdx.length}) →
        (∀ x ∈ B, ∀ y ∈ B, x * y = y * x) → (∀ x ∈ B, x * x = 1) → (iotaC : GL24) ∈ B →
        (∀ x ∈ B, x ≠ 1 → (xFix x).ncard ≠ 2280) → Nat.card B ≤ 16 := CFSG.KD.Co1RankGen.rankC

end Certificates
