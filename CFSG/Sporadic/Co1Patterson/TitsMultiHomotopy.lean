module

public import CFSG.Monster.B.Recog.GenericWalkHomotopy

public section

namespace CFSG.Sporadic.Co1Patterson

open SimpleGraph CFSG.Monster.B.Recog

variable {V : Type*} {G : SimpleGraph V}

inductive ElemMoveBy (T : Set V → Prop) {u v : V} : G.Walk u v → G.Walk u v → Prop
  | backtrack {x y : V} (p : G.Walk u x) (q : G.Walk x v) (h : G.Adj x y) :
      ElemMoveBy T (p.append q) (p.append (.cons h (.cons h.symm q)))
  | triangle {x y z : V} (p : G.Walk u x) (q : G.Walk x v) (hxy : G.Adj x y) (hyz : G.Adj y z)
      (hzx : G.Adj z x) (hT : T {x, y, z}) :
      ElemMoveBy T (p.append q) (p.append (.cons hxy (.cons hyz (.cons hzx q))))

@[expose] def HomotopicBy (T : Set V → Prop) {u v : V} (p q : G.Walk u v) : Prop :=
  Relation.EqvGen (ElemMoveBy T) p q

@[expose] def TriangulableBy (G : SimpleGraph V) (T : Set V → Prop) : Prop :=
  ∀ (u : V) (p : G.Walk u u), HomotopicBy T p .nil

variable {T : Set V → Prop}

namespace HomotopicBy

variable {u v w : V} {p q r : G.Walk u v}

@[refl] theorem refl (p : G.Walk u v) : HomotopicBy T p p := Relation.EqvGen.refl p

@[symm] theorem symm (h : HomotopicBy T p q) : HomotopicBy T q p := Relation.EqvGen.symm _ _ h

@[trans] theorem trans (h₁ : HomotopicBy T p q) (h₂ : HomotopicBy T q r) :
    HomotopicBy T p r :=
  Relation.EqvGen.trans _ _ _ h₁ h₂

end HomotopicBy

theorem ElemMoveBy.homotopicBy {u v : V} {p q : G.Walk u v} (h : ElemMoveBy T p q) :
    HomotopicBy T p q :=
  Relation.EqvGen.rel _ _ h

theorem ElemMoveBy.append_left {w u v : V} (r : G.Walk w u) {p q : G.Walk u v}
    (h : ElemMoveBy T p q) : ElemMoveBy T (r.append p) (r.append q) := by
  cases h with
  | backtrack p q h =>
    rw [Walk.append_assoc, Walk.append_assoc]
    exact .backtrack _ q h
  | triangle p q hxy hyz hzx hT =>
    rw [Walk.append_assoc, Walk.append_assoc]
    exact .triangle _ q hxy hyz hzx hT

theorem ElemMoveBy.append_right {u v w : V} {p q : G.Walk u v} (h : ElemMoveBy T p q)
    (r : G.Walk v w) : ElemMoveBy T (p.append r) (q.append r) := by
  cases h with
  | backtrack p q h =>
    rw [← Walk.append_assoc, ← Walk.append_assoc, Walk.cons_append, Walk.cons_append]
    exact .backtrack p _ h
  | triangle p q hxy hyz hzx hT =>
    rw [← Walk.append_assoc, ← Walk.append_assoc, Walk.cons_append, Walk.cons_append,
      Walk.cons_append]
    exact .triangle p _ hxy hyz hzx hT

theorem ElemMoveBy.reverse {u v : V} {p q : G.Walk u v} (h : ElemMoveBy T p q) :
    ElemMoveBy T p.reverse q.reverse := by
  cases h with
  | backtrack p q h =>
    simp only [Walk.reverse_append, Walk.reverse_cons, ← Walk.append_assoc, Walk.cons_append,
      Walk.nil_append]
    exact .backtrack q.reverse p.reverse h
  | @triangle x y z p q hxy hyz hzx hT =>
    simp only [Walk.reverse_append, Walk.reverse_cons, ← Walk.append_assoc, Walk.cons_append,
      Walk.nil_append]
    refine .triangle q.reverse p.reverse hzx.symm hyz.symm hxy.symm ?_
    rwa [Set.pair_comm z y]

namespace HomotopicBy

variable {u v w : V}

theorem append_left (r : G.Walk w u) {p q : G.Walk u v} (h : HomotopicBy T p q) :
    HomotopicBy T (r.append p) (r.append q) := by
  induction h with
  | rel p q h => exact (h.append_left r).homotopicBy
  | refl p => exact refl _
  | symm p q _ ih => exact ih.symm
  | trans p q r _ _ ih₁ ih₂ => exact ih₁.trans ih₂

theorem append_right {p q : G.Walk u v} (h : HomotopicBy T p q) (r : G.Walk v w) :
    HomotopicBy T (p.append r) (q.append r) := by
  induction h with
  | rel p q h => exact (h.append_right r).homotopicBy
  | refl p => exact refl _
  | symm p q _ ih => exact ih.symm
  | trans p q r _ _ ih₁ ih₂ => exact ih₁.trans ih₂

theorem append {p p' : G.Walk u v} {q q' : G.Walk v w} (hp : HomotopicBy T p p')
    (hq : HomotopicBy T q q') : HomotopicBy T (p.append q) (p'.append q') :=
  (hp.append_right q).trans (hq.append_left p')

theorem cons (h : G.Adj w u) {p q : G.Walk u v} (hpq : HomotopicBy T p q) :
    HomotopicBy T (.cons h p) (.cons h q) := by
  simpa using hpq.append_left (.cons h .nil)

theorem reverse {p q : G.Walk u v} (h : HomotopicBy T p q) :
    HomotopicBy T p.reverse q.reverse := by
  induction h with
  | rel p q h => exact h.reverse.homotopicBy
  | refl p => exact refl _
  | symm p q _ ih => exact ih.symm
  | trans p q r _ _ ih₁ ih₂ => exact ih₁.trans ih₂

end HomotopicBy

theorem homotopicBy_backtrack {u x y v : V} (p : G.Walk u x) (q : G.Walk x v) (h : G.Adj x y) :
    HomotopicBy T (p.append q) (p.append (.cons h (.cons h.symm q))) :=
  (ElemMoveBy.backtrack p q h).homotopicBy

theorem homotopicBy_cons_cons_nil {x y : V} (h : G.Adj x y) :
    HomotopicBy T (.cons h (.cons h.symm .nil) : G.Walk x x) .nil :=
  (homotopicBy_backtrack (.nil : G.Walk x x) .nil h).symm

theorem homotopicBy_cons_cons_symm {x y v : V} (h : G.Adj x y) (w : G.Walk x v) :
    HomotopicBy T (.cons h (.cons h.symm w)) w := by
  simpa using (homotopicBy_backtrack (T := T) (.nil : G.Walk x x) w h).symm

theorem homotopicBy_triangle_nil {x y z : V} (hxy : G.Adj x y) (hyz : G.Adj y z)
    (hzx : G.Adj z x) (hT : T {x, y, z}) :
    HomotopicBy T (.cons hxy (.cons hyz (.cons hzx .nil)) : G.Walk x x) .nil :=
  (ElemMoveBy.triangle .nil .nil hxy hyz hzx hT).homotopicBy.symm

theorem homotopicBy_append_reverse {u v : V} (p : G.Walk u v) :
    HomotopicBy T (p.append p.reverse) .nil := by
  induction p with
  | nil => exact HomotopicBy.refl _
  | @cons a b c h p ih =>
    rw [Walk.reverse_cons, Walk.cons_append, Walk.append_assoc]
    refine (HomotopicBy.cons h (ih.append_right (.cons h.symm .nil))).trans ?_
    exact homotopicBy_cons_cons_nil h

theorem homotopicBy_reverse_append {u v : V} (p : G.Walk u v) :
    HomotopicBy T (p.reverse.append p) .nil := by
  simpa using homotopicBy_append_reverse (T := T) p.reverse

theorem homotopicBy_of_append_reverse {u v : V} {p q : G.Walk u v}
    (h : HomotopicBy T (p.append q.reverse) .nil) : HomotopicBy T p q := by
  have h₁ : HomotopicBy T (p.append (q.reverse.append q)) p := by
    simpa using (homotopicBy_reverse_append (T := T) q).append_left p
  have h₂ : HomotopicBy T ((p.append q.reverse).append q) q := by
    simpa using h.append_right q
  rw [← Walk.append_assoc] at h₂
  exact h₁.symm.trans h₂

theorem HomotopicBy.of_homotopic
    (hT : ∀ (x y z : V) (hxy : G.Adj x y) (hyz : G.Adj y z) (hzx : G.Adj z x),
      HomotopicBy T (.cons hxy (.cons hyz (.cons hzx .nil)) : G.Walk x x) .nil)
    {u v : V} {p q : G.Walk u v} (h : Homotopic p q) : HomotopicBy T p q := by
  induction h with
  | rel p q h =>
    cases h with
    | backtrack p q h => exact (ElemMoveBy.backtrack p q h).homotopicBy
    | @triangle x y z p q hxy hyz hzx =>
      have e := ((hT x y z hxy hyz hzx).append_right q).append_left p
      simp only [Walk.cons_append, Walk.nil_append] at e
      exact e.symm
  | refl p => exact HomotopicBy.refl _
  | symm p q _ ih => exact ih.symm
  | trans p q r _ _ ih₁ ih₂ => exact ih₁.trans ih₂

theorem TriangulableBy.of_triangulable (hG : Triangulable G)
    (hT : ∀ (x y z : V) (hxy : G.Adj x y) (hyz : G.Adj y z) (hzx : G.Adj z x),
      HomotopicBy T (.cons hxy (.cons hyz (.cons hzx .nil)) : G.Walk x x) .nil) :
    TriangulableBy G T :=
  fun u p => HomotopicBy.of_homotopic hT (hG u p)

theorem homotopicBy_triangle_of_cone {x y z v : V} (hxy : G.Adj x y) (hyz : G.Adj y z)
    (hzx : G.Adj z x) (hxv : G.Adj x v) (hyv : G.Adj y v) (hzv : G.Adj z v)
    (h₁ : T {x, y, v}) (h₂ : T {y, z, v}) (h₃ : T {z, x, v}) :
    HomotopicBy T (.cons hxy (.cons hyz (.cons hzx .nil)) : G.Walk x x) .nil := by
  have side : ∀ {s t : V} (hst : G.Adj s t) (hsv : G.Adj s v) (htv : G.Adj t v),
      T {s, t, v} → HomotopicBy T (.cons hst .nil : G.Walk s t) (.cons hsv (.cons htv.symm .nil))
      := by
    intro s t hst hsv htv hT
    refine (homotopicBy_of_append_reverse ?_).symm
    have : T {s, v, t} := by rwa [Set.pair_comm v t]
    simpa using homotopicBy_triangle_nil hsv htv.symm hst.symm this
  have e := (side hxy hxv hyv h₁).append ((side hyz hyv hzv h₂).append (side hzx hzv hxv h₃))
  simp only [Walk.cons_append, Walk.nil_append] at e
  refine e.trans ?_
  refine (((homotopicBy_cons_cons_symm hyv.symm _).trans
    (homotopicBy_cons_cons_symm hzv.symm _)).cons hxv).trans ?_
  exact homotopicBy_cons_cons_nil hxv

theorem ElemMoveBy.map (f : G →g G) (hf : ∀ x y z, T {x, y, z} → T {f x, f y, f z})
    {u v : V} {p q : G.Walk u v} (h : ElemMoveBy T p q) :
    ElemMoveBy T (p.map f) (q.map f) := by
  cases h with
  | backtrack p q h =>
    simp only [Walk.map_append, Walk.map_cons]
    exact .backtrack _ _ (f.map_adj h)
  | triangle p q hxy hyz hzx hT =>
    simp only [Walk.map_append, Walk.map_cons]
    exact .triangle _ _ (f.map_adj hxy) (f.map_adj hyz) (f.map_adj hzx) (hf _ _ _ hT)

theorem HomotopicBy.map (f : G →g G) (hf : ∀ x y z, T {x, y, z} → T {f x, f y, f z})
    {u v : V} {p q : G.Walk u v} (h : HomotopicBy T p q) :
    HomotopicBy T (p.map f) (q.map f) := by
  induction h with
  | rel p q h => exact (h.map f hf).homotopicBy
  | refl p => exact HomotopicBy.refl _
  | symm p q _ ih => exact ih.symm
  | trans p q r _ _ ih₁ ih₂ => exact ih₁.trans ih₂

end CFSG.Sporadic.Co1Patterson
