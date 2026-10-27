module

public import CFSG.RankThree.PartOne.SLB4A.Index

public section

namespace CFSG.RankThree.PartOne.SLB4A

open TauCeti CFSG

@[expose] def IsTypeEOddIndex : CFSGIndex → Prop
  | .lie ⟨.E6 q, _⟩ => q.p ≠ 2
  | .lie ⟨.E7 q, _⟩ => q.p ≠ 2
  | .lie ⟨.E8 q, _⟩ => q.p ≠ 2
  | _ => False

@[expose] def IsTypeEEvenIndex : CFSGIndex → Prop
  | .lie ⟨.E6 q, _⟩ => q.p = 2
  | .lie ⟨.E7 q, _⟩ => q.p = 2
  | .lie ⟨.E8 q, _⟩ => q.p = 2
  | _ => False

@[expose] def IsTypeF4OddIndex : CFSGIndex → Prop
  | .lie ⟨.F4 q, _⟩ => q.p ≠ 2
  | _ => False

@[expose] def IsTypeF4EvenIndex : CFSGIndex → Prop
  | .lie ⟨.F4 q, _⟩ => q.p = 2
  | _ => False

@[expose] def IsTypeTwistedE6OddIndex : CFSGIndex → Prop
  | .lie ⟨.twistedE6 q, _⟩ => q.p ≠ 2
  | _ => False

@[expose] def IsTypeTwistedE6EvenIndex : CFSGIndex → Prop
  | .lie ⟨.twistedE6 q, _⟩ => q.p = 2
  | _ => False

end CFSG.RankThree.PartOne.SLB4A
