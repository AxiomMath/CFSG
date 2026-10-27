module

public import CFSG.Sporadic.Co1Patterson.TitsMultiHomotopy

public section

namespace CFSG.Sporadic.Co1Patterson

open SimpleGraph CFSG.Monster.B.Recog

variable {V : Type*} {G : SimpleGraph V} {T : Set V → Prop}

theorem ElemMoveBy.elemMove {u v : V} {p q : G.Walk u v} (h : ElemMoveBy T p q) :
    ElemMove p q := by
  cases h with
  | backtrack p q h => exact .backtrack p q h
  | triangle p q hxy hyz hzx _ => exact .triangle p q hxy hyz hzx

theorem HomotopicBy.homotopic {u v : V} {p q : G.Walk u v} (h : HomotopicBy T p q) :
    Homotopic p q := by
  induction h with
  | rel _ _ h => exact Relation.EqvGen.rel _ _ h.elemMove
  | refl => exact Relation.EqvGen.refl _
  | symm _ _ _ ih => exact Relation.EqvGen.symm _ _ ih
  | trans _ _ _ _ _ ih₁ ih₂ => exact Relation.EqvGen.trans _ _ _ ih₁ ih₂

theorem TriangulableBy.triangulable (h : TriangulableBy G T) : Triangulable G :=
  fun u p => (h u p).homotopic

end CFSG.Sporadic.Co1Patterson
