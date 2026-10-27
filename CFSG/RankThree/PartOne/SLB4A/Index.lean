module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.ElementaryAbelian
public import TauCeti.GroupTheory.SpecificGroups.CFSG.Classification

public section

namespace CFSG.RankThree.PartOne.SLB4A

open TauCeti CFSG

@[expose] def TwoPowFiveOf (P : CFSGIndex → Prop) : Prop :=
  ∀ i : CFSGIndex, P i → ∀ (T : Type) [Group T], Nonempty (T ≃* i.Group) →
    ∃ U : Subgroup T, IsElementaryAbelian 2 U ∧ Nat.card U = 2 ^ (3 + 2)

theorem TwoPowFiveOf.union {P Q : CFSGIndex → Prop} (hP : TwoPowFiveOf P) (hQ : TwoPowFiveOf Q) :
    TwoPowFiveOf (fun i => P i ∨ Q i) :=
  fun i hi T _ e => hi.elim (fun h => hP i h T e) (fun h => hQ i h T e)

@[expose] def IsTypeAIndex : CFSGIndex → Prop
  | .lie ⟨.A r q, _⟩ =>
      (q.p = 2 ∧ 4 ≤ r) ∨ (q.p ≠ 2 ∧ r = 5 ∧ q.card % 4 = 1) ∨ (q.p ≠ 2 ∧ 6 ≤ r)
  | _ => False

@[expose] def IsTypeTwistedAIndex : CFSGIndex → Prop
  | .lie ⟨.twistedA r q, _⟩ =>
      (q.p = 2 ∧ 5 ≤ r) ∨ (q.p ≠ 2 ∧ r = 5 ∧ q.card % 4 = 3) ∨ (q.p ≠ 2 ∧ 6 ≤ r)
  | _ => False

@[expose] def IsTypeCIndex : CFSGIndex → Prop
  | .lie ⟨.C r _, _⟩ => 4 ≤ r
  | _ => False

@[expose] def IsTypeBEvenIndex : CFSGIndex → Prop
  | .lie ⟨.B r q, _⟩ => q.p = 2 ∧ 4 ≤ r
  | _ => False

@[expose] def IsTypeBOddIndex : CFSGIndex → Prop
  | .lie ⟨.B r q, _⟩ => q.p ≠ 2 ∧ 3 ≤ r
  | _ => False

@[expose] def IsTypeDIndex : CFSGIndex → Prop
  | .lie ⟨.D r _, _⟩ => 4 ≤ r
  | _ => False

@[expose] def IsTypeTwistedDIndex : CFSGIndex → Prop
  | .lie ⟨.twistedD r q, _⟩ => (q.p ≠ 2 ∧ 4 ≤ r) ∨ (q.p = 2 ∧ 5 ≤ r)
  | _ => False

end CFSG.RankThree.PartOne.SLB4A
