module

public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.RankThree.PartOne.N143.SectionCover

public section

namespace CFSG.RankThree.PartOne.N143

open CFSG TauCeti

@[expose] def IsLieThreeIndex : CFSGIndex → Prop
  | .lie ⟨.A r q, _⟩ => r = 2 ∧ 3 ∣ q.card - 1
  | .lie ⟨.twistedA r q, _⟩ => r = 2 ∧ 3 ∣ q.card + 1
  | _ => False

@[expose] def IsLieHighIndex : CFSGIndex → Prop
  | .lie ⟨.A r q, _⟩ => 5 ≤ r ∧ 3 ∣ r + 1 ∧ 3 ∣ q.card - 1
  | .lie ⟨.twistedA r q, _⟩ => 5 ≤ r ∧ 3 ∣ r + 1 ∧ 3 ∣ q.card + 1
  | _ => False

@[expose] def IsLieSmallIndex : CFSGIndex → Prop
  | .lie ⟨.twistedA r q, _⟩ => r = 3 ∧ q.card = 3
  | .lie ⟨.G2 q, _⟩ => q.card = 3
  | _ => False

@[expose] def IsLieO7Index : CFSGIndex → Prop
  | .lie ⟨.B r q, _⟩ => r = 3 ∧ q.card = 3
  | _ => False

@[expose] def IsLieE6Index : CFSGIndex → Prop
  | .lie ⟨.E6 q, _⟩ => 3 ∣ q.card - 1
  | .lie ⟨.twistedE6 q, _⟩ => 3 ∣ q.card + 1
  | _ => False

end CFSG.RankThree.PartOne.N143
