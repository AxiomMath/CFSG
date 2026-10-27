module

public import CFSG.RankThree.PartOne.KF.UnitaryTorus
public import CFSG.ClassicalGroups.UnitaryFlag.GroupData

public section

namespace CFSG.RankThree.PartTwo.Sec21

open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
open CFSG.RankThree.PartOne.KFU (torusSU)

@[expose] def Item2115U4KConjTorus : Prop :=
  ∀ (f : ℕ) (K : Type) [Field K], UnitaryFieldData 2 f K → 2 ≤ f → 3 ∣ 2 ^ f + 1 →
    ∀ g ∈ unitarySU 2 f K 4, g ^ 3 = 1 →
      ∃ u ∈ unitarySU 2 f K 4, u * g * u⁻¹ ∈ torusSU 3 4 K

@[expose] def Item2115U4KTorusE27 : Prop :=
  ∀ (f : ℕ) (K : Type) [Field K], UnitaryFieldData 2 f K → 2 ≤ f → 3 ∣ 2 ^ f + 1 →
    ∀ F : Subgroup (GL (Fin 4) K), F ≤ unitarySU 2 f K 4 → CFSG.Assembly.IsElemAbelian 3 F →
      3 ^ 3 ≤ Nat.card F → F ≤ Subgroup.normalizer (torusSU 3 4 K : Set (GL (Fin 4) K)) →
      F ≤ torusSU 3 4 K

end CFSG.RankThree.PartTwo.Sec21
