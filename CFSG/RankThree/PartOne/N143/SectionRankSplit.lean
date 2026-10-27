module

public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Foundations.Catalog
import CFSG.Adapters.ProjectiveSpecialLinear

public section

namespace CFSG.RankThree.PartOne.N143

open CFSG CFSG.Assembly TauCeti Subgroup
open CFSG.Assembly.LowTwoRank (StatedClassicalModel)

@[expose] def IsAlternatingIndex : CFSGIndex → Prop
  | .alternating _ _ => True
  | _ => False

@[expose] def IsSporadicIndex : CFSGIndex → Prop
  | .sporadic _ => True
  | _ => False

@[expose] def IsLieIndex : CFSGIndex → Prop
  | .lie _ => True
  | _ => False

@[expose] def OddCentralCoverRank3For (P : CFSGIndex → Prop) : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y], CFSG.IsKGroup Y → Group.IsPerfect Y → CFSG.Assembly.evenRank Y ≤ 3 →
    ∀ (S : Type) [Group S] [Finite S] [IsSimpleGroup S], (∃ a b : S, a * b ≠ b * a) →
      ∀ φ : Y →* S, Function.Surjective φ → φ.ker ≤ center Y → IsPGroup 3 φ.ker → 3 ∣ Nat.card φ.ker →
        (∃ i : CFSGIndex, P i ∧ Nonempty (S ≃* i.Group)) → CFSG.Assembly.evenRank S ≤ 3

end CFSG.RankThree.PartOne.N143
