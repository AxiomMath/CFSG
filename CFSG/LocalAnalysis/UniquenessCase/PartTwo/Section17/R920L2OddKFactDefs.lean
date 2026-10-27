module

public import CFSG.LocalAnalysis.UniquenessCase.UCFront09b

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17

open Subgroup CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22

structure KCfgL2Odd {Q : Type} [Group Q] (X W T : Subgroup Q) (n r : ℕ) : Prop where
  isL2 : IsL2 (Bar2 X) n
  odd : Odd n
  five_le : 5 ≤ n
  r_prime : r.Prime
  r_dvd : r ∣ 2 ^ n - 1
  X_le : X ≤ W
  T_le : T ≤ W
  T_sylow : CFSG.ABGLocalTools.IsSylowOf 2 T ⊤
  N3 : ∀ E : Subgroup Q, E ≤ X → Nat.card E = 3 → normalizer (E : Set Q) ≤ W
  Nr : ∀ B : Subgroup Q, B ≤ X → Nat.card B = r → ∀ P : Subgroup Q, IsPGroup r ↥P → B ≤ P →
    normalizer (P : Set Q) ≤ W

@[expose] def KFactShape92L2Odd : Prop :=
  ∀ (Q : Type) [Group Q] [Finite Q], F09.Shape92 Q →
    (∀ P : Subgroup Q, IsPGroup 3 ↥P → IsCyclic ↥P) →
    ∀ (X W T : Subgroup Q) (n r : ℕ), KCfgL2Odd X W T n r → W = ⊤

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17
