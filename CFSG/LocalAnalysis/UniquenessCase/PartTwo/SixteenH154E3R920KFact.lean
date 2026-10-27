module

public import CFSG.LocalAnalysis.UniquenessCase.UC22Defs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

structure KCfgL28 {Q : Type} [Group Q] (X W T : Subgroup Q) : Prop where
  isL2 : IsL2 (Bar2 X) 3
  X_le : X ≤ W
  T_le : T ≤ W
  T_sylow : CFSG.ABGLocalTools.IsSylowOf 2 T ⊤
  N3 : ∀ E : Subgroup Q, E ≤ X → Nat.card E = 3 → normalizer (E : Set Q) ≤ W
  N7 : ∀ B : Subgroup Q, B ≤ X → Nat.card B = 7 → ∀ P : Subgroup Q, IsPGroup 7 ↥P → B ≤ P →
    normalizer (P : Set Q) ≤ W

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
