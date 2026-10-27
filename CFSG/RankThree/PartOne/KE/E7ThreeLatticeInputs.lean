module

public import CFSG.RankThree.PartOne.KE.Rank3Lines
public import CFSG.RankThree.PartOne.KE.E7ClassLists
public import CFSG.RankThree.PartOne.KE.E7TwelveLattice
public meta import CFSG.RankThree.PartOne.KE.Rank3Lines
public meta import CFSG.RankThree.PartOne.KE.E7ClassLists
public meta import CFSG.RankThree.PartOne.KE.E7TwelveLattice
public import CFSG.LieType.Ree.LargeReeSylowOpposition
public meta import CFSG.LieType.Ree.LargeReeSylowOpposition
public import CFSG.LinearAlgebra.LinearGroups.LinearTwo
public meta import CFSG.LinearAlgebra.LinearGroups.LinearTwo
public meta import CFSG.Monster.B.Geometry.CoxeterWords
public import CFSG.Monster.B.Geometry.CoxeterWords
public import CFSG.RankThree.PartOne.KE.A1Action
public meta import CFSG.RankThree.PartOne.KE.A1Action
public import CFSG.RankThree.PartOne.KE.A1Levi
public meta import CFSG.RankThree.PartOne.KE.A1Levi
public import CFSG.RankThree.PartOne.KE.E7FourLattice
public meta import CFSG.RankThree.PartOne.KE.E7FourLattice
public import CFSG.RankThree.PartOne.KE.SigmaUntwisted
public meta import CFSG.RankThree.PartOne.KE.SigmaUntwisted
public meta import CFSG.RankThree.PartOne.KE.ThreeA1Group
public import CFSG.RankThree.PartOne.KE.ThreeA1Group
public meta import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.FiniteFieldFixedSubfieldCard
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.FiniteFieldFixedSubfieldCard
public import CFSG.Walter.Defs
public meta import CFSG.Walter.Defs

public section

namespace CFSG.RankThree.PartOne.KE

open Matrix CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.RankThree.Chevalley CFSG.RankThree.Lattice
open scoped Matrix

section Defs

@[expose] def e7T3Word : List (Fin Tag.E7.rank) :=
  [0, 1, 2, 3, 4, 5, 0, 1, 2, 3, 4, 5, 0, 1, 2, 3, 4, 5, 0, 1, 2, 3, 4, 5]

@[expose] def e7T3W : Matrix (Fin Tag.E7.rank) (Fin Tag.E7.rank) ℤ := e7T12W ^ 4

@[expose] def e7T3WList : List (List ℤ) :=
  lmul Tag.E7.rank e7T12WList (lmul Tag.E7.rank e7T12WList
    (lmul Tag.E7.rank e7T12WList e7T12WList))

theorem e7T3W_eq : e7T3W = toMat Tag.E7.rank e7T3WList := by
  rw [e7T3W, pow_succ', pow_succ', pow_succ', pow_one, e7T12W_eq, e7T3WList, toMat_lmul,
    toMat_lmul, toMat_lmul]

theorem e7wl_e7T3Word : e7wl e7T3Word = e7T3WList := by decide +kernel

@[expose] def e7T3FList : List ℤ := [2, 3, 4, 6, 5, 4, 3]

@[expose] def e7T3B1List : List ℤ := [0, 0, 0, 1, 1, 1, 0]

@[expose] def e7T3B2List : List ℤ := [0, 1, 1, 1, 1, 1, 1]

@[expose] def e7T3B3List : List ℤ := [1, 2, 2, 3, 2, 2, 1]

@[expose] def e7T3ColsList : List (List ℤ) :=
  [e7T3FList, e7T3B1List, lmulVec Tag.E7.rank e7T3WList e7T3B1List, e7T3B2List,
    lmulVec Tag.E7.rank e7T3WList e7T3B2List, e7T3B3List,
    lmulVec Tag.E7.rank e7T3WList e7T3B3List]

end Defs

section Certs

structure E7T3Comp where
  kind : ℕ
  u : List (Fin Tag.E7.rank)
  rot : Bool
  deriving Inhabited

structure E7T3Cert where
  cls : List ℕ
  w : List (Fin Tag.E7.rank)
  comps : List E7T3Comp
  deriving Inhabited

@[expose] def e7T3Nodes : ℕ → List ℕ
  | 0 => [0, 2]
  | 1 => [1, 4, 6]
  | 2 => [1, 2, 3, 4]
  | _ => [1, 3, 4, 5, 6]

@[expose] def e7StdRoots (J : List ℕ) : List (List ℤ) :=
  Tag.E7.artifactRoots.filter fun l => (List.range 7).all fun k => decide (k ∈ J) || vget l k == 0

@[expose] def e7perm3 (a b c : ℕ) (l : List ℤ) : List ℤ :=
  List.ofFn fun k : Fin Tag.E7.rank =>
    vget l (if k.val = a then c else if k.val = b then a else if k.val = c then b else k.val)

@[expose] def e7T3Perm (kind : ℕ) (rot : Bool) (l : List ℤ) : List ℤ :=
  if kind = 1 then (if rot then e7perm3 1 6 4 l else e7perm3 1 4 6 l)
  else if kind = 2 then (if rot then e7perm3 1 4 2 l else e7perm3 1 2 4 l) else l

@[expose] def E7T3Comp.Good (ww w : List (Fin Tag.E7.rank)) (c : E7T3Comp) : Prop :=
  (∀ x ∈ c.u, x.val ∈ e7T3Nodes c.kind) ∧ c.kind < 4 ∧ (c.kind = 1 → c.u = []) ∧
    ∀ l ∈ e7StdRoots (e7T3Nodes c.kind),
      lmulVec Tag.E7.rank (e7wl (w.reverse ++ ww ++ w)) l =
        lmulVec Tag.E7.rank (e7wl c.u) (e7T3Perm c.kind c.rot l)

instance instDecidableE7T3CompGood (ww w : List (Fin Tag.E7.rank)) (c : E7T3Comp) :
    Decidable (c.Good ww w) := by
  unfold E7T3Comp.Good
  infer_instance

@[expose] def e7T3NegD4 : List (Fin Tag.E7.rank) := [4, 3, 2, 1, 3, 4, 3, 2, 1, 3, 2, 1]

@[expose] def E7T3Cert.rootList (c : E7T3Cert) : List (List ℤ) :=
  c.comps.flatMap fun cm =>
    (e7StdRoots (e7T3Nodes cm.kind)).map (lmulVec Tag.E7.rank (e7wl c.w))

end Certs


section Lists

@[expose] def e7T3Rows : List ERow := [
    ((1, 1), (1, 1), (0, 0)),
    ((0, 1), (-1, 0), (0, 0)),
    ((0, 0), (1, 0), (-1, -1)),
    ((1, 1), (1, 2), (0, -1)),
    ((0, 0), (0, 0), (-1, 0)),
    ((1, 0), (1, 0), (-1, -1)),
    ((1, 1), (1, 1), (-1, -1)),
    ((-1, 0), (-1, -1), (0, 1)),
    ((0, 0), (0, -1), (0, 0)),
    ((0, 1), (0, 0), (0, 0)),
    ((0, 1), (-1, 1), (1, 1)),
    ((1, 2), (0, 2), (1, 0)),
    ((0, 1), (-1, 0), (0, 1)),
    ((1, 1), (2, 2), (0, -1)),
    ((0, 0), (1, 0), (-1, 0)),
    ((1, 1), (1, 2), (0, 0)),
    ((0, 1), (0, 1), (1, 1)),
    ((0, 0), (0, -1), (-1, -1)),
    ((1, 1), (0, 1), (0, -1)),
    ((1, 0), (2, 1), (-1, -2)),
    ((-1, 0), (-2, -2), (0, 1))]

@[expose] def e7T3BinvList : List (List ℤ) := [
    [1, 0, 0, -1, 1, 0, 0],
    [-1, -1, 0, 1, -1, 1, 0],
    [0, 0, -1, 1, -1, 0, 1],
    [-2, -1, 2, 0, -1, 1, 0],
    [-1, -1, 0, 2, -2, 0, 1],
    [0, 1, -1, 1, -1, 0, 0],
    [0, 1, -1, 0, 1, -1, 0]]


end Lists

section Rows

@[expose] def e7T3Row (l : List ℤ) : ERow :=
  ((vget (lmulVec Tag.E7.rank e7T3BinvList l) 1, vget (lmulVec Tag.E7.rank e7T3BinvList l) 2),
    (vget (lmulVec Tag.E7.rank e7T3BinvList l) 3, vget (lmulVec Tag.E7.rank e7T3BinvList l) 4),
    (vget (lmulVec Tag.E7.rank e7T3BinvList l) 5, vget (lmulVec Tag.E7.rank e7T3BinvList l) 6))

@[expose] def e7T3G (i : ℕ) : ERow := e7T3Rows.getD i default

@[expose] def RowIs (l : List ℤ) (i : ℕ) : Prop :=
  ∃ u ∈ eUnits, e7T3Row l = escale u (e7T3G i)

instance instDecidableE7T3RowIs (l : List ℤ) (i : ℕ) : Decidable (RowIs l i) := by
  unfold RowIs
  infer_instance

@[expose] def E7T3Cert.Good (c : E7T3Cert) : Prop :=
  (∀ cm ∈ c.comps, cm.Good e7T3Word c.w) ∧ (∀ i ∈ c.cls, i < 21) ∧
    (∀ r ∈ c.rootList, r ∈ Tag.E7.artifactRoots) ∧
    ∀ r ∈ Tag.E7.artifactRoots, (∃ i ∈ c.cls, RowIs r i) ↔ r ∈ c.rootList

instance instDecidableE7T3CertGood (c : E7T3Cert) : Decidable c.Good := by
  unfold E7T3Cert.Good
  infer_instance

end Rows

section CertData

@[expose] def e7T3Certs : List E7T3Cert := [
  { cls := [0], w := [5, 6, 0, 2, 3, 4, 5, 1, 3, 4, 2, 3, 0, 2, 1, 3, 4, 5, 2, 3, 0, 2, 1, 3],
    comps := [{ kind := 1, u := [], rot := true }] },
  { cls := [0, 1, 8, 9, 15], w := [2, 3, 4, 5, 6, 0, 2, 3, 4, 5, 3, 2, 1, 3, 4, 3, 2, 1, 3, 0, 2],
    comps := [{ kind := 3, u := [6, 5, 1, 3], rot := false }] },
  { cls := [0, 2, 10, 12, 13], w := [5, 6, 3, 0, 2, 1, 3, 4, 5, 3, 2, 1, 3, 4, 3, 2, 1, 3, 0, 2],
    comps := [{ kind := 3, u := [6, 5, 1, 3], rot := false }] },
  { cls := [0, 3, 7, 11, 14], w := [4, 5, 6, 0, 2, 3, 4, 5, 3, 2, 1, 3, 4, 3, 2, 1, 3, 0, 2],
    comps := [{ kind := 3, u := [6, 5, 1, 3], rot := false }] },
  { cls := [0, 4, 5, 6, 16], w := [4, 5, 6, 0, 2, 1, 3, 4, 5, 2, 3, 0, 2, 1, 3, 4, 3, 2, 1, 3, 0, 2],
    comps := [{ kind := 3, u := [6, 5, 1, 3], rot := false }] },
  { cls := [0, 17], w := [3, 0, 2, 1, 3, 4, 5, 6, 4, 5, 3, 4, 2, 3, 0, 2, 1, 3, 4, 5, 2, 1, 3, 4, 0, 2, 3],
    comps := [{ kind := 0, u := [0, 2], rot := false }, { kind := 1, u := [], rot := true }] },
  { cls := [0, 18], w := [5, 4, 2, 3, 0, 2, 1, 3, 4, 5, 6, 5, 4, 3, 2, 1, 3, 4, 5, 4, 2, 3, 0, 2, 1, 3],
    comps := [{ kind := 0, u := [2, 0], rot := false }, { kind := 1, u := [], rot := true }] },
  { cls := [0, 19], w := [5, 4, 3, 0, 2, 1, 3, 4, 5, 6, 5, 4, 3, 2, 1, 3, 4, 5, 2, 1, 3, 4, 0, 2, 3],
    comps := [{ kind := 0, u := [0, 2], rot := false }, { kind := 1, u := [], rot := false }] },
  { cls := [0, 20], w := [5, 6, 0, 2, 3, 4, 5, 1, 3, 4, 2, 3, 0, 2, 1, 3, 4, 5, 2, 3, 0, 2, 1, 3],
    comps := [{ kind := 0, u := [2, 0], rot := false }, { kind := 1, u := [], rot := true }] },
  { cls := [1], w := [2, 3, 4, 5, 6, 5, 4, 3, 0, 2, 1, 3, 4, 5, 2, 3, 0, 2, 1, 3],
    comps := [{ kind := 1, u := [], rot := true }] },
  { cls := [1, 2, 3, 6, 20], w := [1, 3, 4, 5, 6, 2, 3, 4, 5, 1, 3, 4, 3, 2, 1, 3, 0, 2],
    comps := [{ kind := 3, u := [6, 5, 3, 1], rot := false }] },
  { cls := [1, 4, 7, 12, 18], w := [5, 6, 2, 3, 4, 5, 1, 3, 4, 3, 2, 1, 3, 0, 2],
    comps := [{ kind := 3, u := [5, 6, 3, 1], rot := false }] },
  { cls := [1, 5, 10, 11, 17], w := [6, 2, 3, 4, 5, 3, 0, 2, 1, 3, 4, 3, 2, 1, 3, 0, 2],
    comps := [{ kind := 3, u := [5, 6, 1, 3], rot := false }] },
  { cls := [1, 13], w := [4, 3, 2, 1, 3, 4, 5, 6, 5, 4, 2, 3, 0, 2, 1, 3, 4, 5, 2, 1, 3, 4, 0, 2, 3],
    comps := [{ kind := 0, u := [0, 2], rot := false }, { kind := 1, u := [], rot := false }] },
  { cls := [1, 14], w := [3, 2, 1, 3, 4, 5, 6, 5, 4, 2, 3, 0, 2, 1, 3, 4, 5, 4, 2, 3, 0, 2, 1, 3],
    comps := [{ kind := 0, u := [2, 0], rot := false }, { kind := 1, u := [], rot := true }] },
  { cls := [1, 16], w := [2, 3, 4, 5, 6, 5, 4, 3, 0, 2, 1, 3, 4, 5, 2, 1, 3, 4, 0, 2, 3],
    comps := [{ kind := 0, u := [0, 2], rot := false }, { kind := 1, u := [], rot := false }] },
  { cls := [1, 19], w := [2, 1, 3, 4, 5, 6, 5, 4, 3, 2, 1, 3, 4, 5, 2, 3, 0, 2, 1, 3],
    comps := [{ kind := 0, u := [2, 0], rot := false }, { kind := 1, u := [], rot := false }] },
  { cls := [2], w := [3, 4, 5, 6, 5, 4, 2, 3, 0, 2, 1, 3, 4, 5, 2, 3, 0, 2, 1, 3],
    comps := [{ kind := 1, u := [], rot := true }] },
  { cls := [2, 4, 8, 14, 17], w := [5, 6, 3, 4, 5, 2, 1, 3, 4, 3, 2, 1, 3, 0, 2],
    comps := [{ kind := 3, u := [5, 6, 3, 1], rot := false }] },
  { cls := [2, 5, 7, 9, 19], w := [6, 3, 4, 5, 2, 3, 0, 2, 1, 3, 4, 3, 2, 1, 3, 0, 2],
    comps := [{ kind := 3, u := [5, 6, 1, 3], rot := false }] },
  { cls := [2, 11], w := [3, 4, 2, 3, 0, 2, 1, 3, 4, 5, 6, 5, 4, 3, 0, 2, 1, 3, 4, 5, 1, 3, 4, 0, 2, 1, 3],
    comps := [{ kind := 0, u := [0, 2], rot := false }, { kind := 1, u := [], rot := true }] },
  { cls := [2, 15], w := [1, 3, 4, 5, 6, 5, 4, 2, 3, 0, 2, 1, 3, 4, 5, 4, 2, 3, 0, 2, 1, 3],
    comps := [{ kind := 0, u := [2, 0], rot := false }, { kind := 1, u := [], rot := true }] },
  { cls := [2, 16], w := [3, 4, 5, 6, 5, 4, 2, 3, 0, 2, 1, 3, 4, 5, 2, 1, 3, 4, 0, 2, 3],
    comps := [{ kind := 0, u := [0, 2], rot := false }, { kind := 1, u := [], rot := false }] },
  { cls := [2, 18], w := [3, 2, 1, 3, 4, 5, 6, 5, 4, 3, 2, 1, 3, 4, 5, 3, 0, 2, 1, 3],
    comps := [{ kind := 0, u := [2, 0], rot := false }, { kind := 1, u := [], rot := false }] },
  { cls := [3], w := [4, 5, 6, 5, 4, 3, 0, 2, 1, 3, 4, 5, 2, 3, 0, 2, 1, 3],
    comps := [{ kind := 1, u := [], rot := true }] },
  { cls := [3, 4, 10, 15, 19], w := [5, 6, 4, 5, 1, 3, 4, 3, 2, 1, 3, 0, 2],
    comps := [{ kind := 3, u := [5, 6, 3, 1], rot := false }] },
  { cls := [3, 5, 8, 13, 18], w := [6, 4, 5, 3, 0, 2, 1, 3, 4, 3, 2, 1, 3, 0, 2],
    comps := [{ kind := 3, u := [5, 6, 1, 3], rot := false }] },
  { cls := [3, 9], w := [4, 3, 0, 2, 1, 3, 4, 5, 6, 5, 4, 3, 0, 2, 1, 3, 4, 5, 1, 3, 4, 0, 2, 1, 3],
    comps := [{ kind := 0, u := [0, 2], rot := false }, { kind := 1, u := [], rot := true }] },
  { cls := [3, 12], w := [5, 6, 4, 5, 1, 3, 4, 2, 3, 0, 2, 1, 3, 4, 5, 3, 4, 3, 0, 2, 1, 3],
    comps := [{ kind := 0, u := [2, 0], rot := false }, { kind := 1, u := [], rot := false }] },
  { cls := [3, 16], w := [4, 5, 6, 5, 4, 3, 0, 2, 1, 3, 4, 5, 2, 1, 3, 4, 0, 2, 3],
    comps := [{ kind := 0, u := [0, 2], rot := false }, { kind := 1, u := [], rot := false }] },
  { cls := [3, 17], w := [1, 3, 4, 5, 6, 5, 4, 3, 2, 1, 3, 4, 5, 3, 0, 2, 1, 3],
    comps := [{ kind := 0, u := [2, 0], rot := false }, { kind := 1, u := [], rot := false }] },
  { cls := [4], w := [5, 6, 5, 4, 3, 2, 1, 3, 4, 5, 2, 3, 0, 2, 1, 3],
    comps := [{ kind := 1, u := [], rot := false }] },
  { cls := [4, 9], w := [3, 2, 1, 3, 4, 5, 6, 5, 4, 3, 0, 2, 1, 3, 4, 5, 1, 3, 4, 0, 2, 1, 3],
    comps := [{ kind := 0, u := [0, 2], rot := false }, { kind := 1, u := [], rot := false }] },
  { cls := [4, 11], w := [2, 1, 3, 4, 5, 6, 5, 4, 3, 0, 2, 1, 3, 4, 5, 3, 4, 3, 0, 2, 1, 3],
    comps := [{ kind := 0, u := [2, 0], rot := false }, { kind := 1, u := [], rot := true }] },
  { cls := [4, 13], w := [1, 3, 4, 5, 6, 5, 4, 3, 0, 2, 1, 3, 4, 5, 1, 3, 4, 0, 2, 1, 3],
    comps := [{ kind := 0, u := [0, 2], rot := false }, { kind := 1, u := [], rot := false }] },
  { cls := [4, 20], w := [5, 6, 5, 4, 3, 2, 1, 3, 4, 5, 2, 3, 0, 2, 1, 3],
    comps := [{ kind := 0, u := [2, 0], rot := false }, { kind := 1, u := [], rot := false }] },
  { cls := [5], w := [6, 4, 5, 3, 4, 2, 3, 0, 2, 1, 3, 4, 5, 2, 3, 0, 2, 1, 3],
    comps := [{ kind := 1, u := [], rot := false }] },
  { cls := [5, 12], w := [2, 3, 4, 5, 6, 5, 1, 3, 4, 2, 3, 0, 2, 1, 3, 4, 5, 4, 2, 3, 0, 2, 1, 3],
    comps := [{ kind := 0, u := [2, 0], rot := false }, { kind := 1, u := [], rot := true }] },
  { cls := [5, 14], w := [4, 3, 0, 2, 1, 3, 4, 5, 6, 5, 4, 3, 2, 1, 3, 4, 5, 3, 4, 0, 2, 1, 3],
    comps := [{ kind := 0, u := [0, 2], rot := false }, { kind := 1, u := [], rot := true }] },
  { cls := [5, 15], w := [4, 5, 6, 5, 1, 3, 4, 2, 3, 0, 2, 1, 3, 4, 5, 4, 2, 3, 0, 2, 1, 3],
    comps := [{ kind := 0, u := [2, 0], rot := false }, { kind := 1, u := [], rot := true }] },
  { cls := [5, 20], w := [6, 4, 5, 3, 4, 2, 3, 0, 2, 1, 3, 4, 5, 2, 3, 4, 0, 2, 3],
    comps := [{ kind := 0, u := [0, 2], rot := false }, { kind := 1, u := [], rot := true }] },
  { cls := [6], w := [1, 3, 4, 5, 2, 3, 4, 1, 3],
    comps := [{ kind := 0, u := [0, 2], rot := false }] },
  { cls := [6, 7], w := [2, 1, 3, 4, 5, 6, 4, 5, 1, 3, 4, 2, 3, 0, 2, 1, 3, 4, 5, 3, 4, 3, 0, 2, 1, 3],
    comps := [{ kind := 0, u := [2, 0], rot := false }, { kind := 1, u := [], rot := false }] },
  { cls := [6, 8], w := [1, 3, 4, 5, 6, 5, 1, 3, 4, 2, 3, 0, 2, 1, 3, 4, 5, 3, 4, 3, 0, 2, 1, 3],
    comps := [{ kind := 0, u := [2, 0], rot := false }, { kind := 1, u := [], rot := true }] },
  { cls := [6, 9, 14, 18], w := [3, 2, 1, 3, 4, 5, 3, 2, 0],
    comps := [{ kind := 2, u := [3, 2, 1, 3, 4, 1, 3, 2], rot := true }] },
  { cls := [6, 10], w := [1, 3, 4, 5, 6, 4, 5, 3, 4, 2, 3, 0, 2, 1, 3, 4, 5, 3, 4, 3, 0, 2, 1, 3],
    comps := [{ kind := 0, u := [2, 0], rot := false }, { kind := 1, u := [], rot := false }] },
  { cls := [6, 11, 12, 19], w := [2, 1, 3, 4, 5, 1, 3, 2, 0],
    comps := [{ kind := 2, u := [3, 2, 1, 3, 4, 1, 3, 2], rot := true }] },
  { cls := [6, 13, 15, 17], w := [1, 3, 4, 5, 3, 2, 0],
    comps := [{ kind := 2, u := [3, 2, 1, 3, 4, 1, 3, 2], rot := true }] },
  { cls := [7], w := [6, 5, 3, 4, 2, 3, 0, 2, 1, 3, 4, 5, 3, 0, 2, 1, 3],
    comps := [{ kind := 1, u := [], rot := false }] },
  { cls := [7, 8, 10, 16, 20], w := [6, 5, 0, 2, 3, 4, 3, 2, 1, 3, 0, 2],
    comps := [{ kind := 3, u := [5, 6, 3, 1], rot := false }] },
  { cls := [7, 13], w := [0, 2, 3, 4, 5, 6, 5, 4, 3, 2, 1, 3, 4, 5, 1, 3, 4, 0, 2, 1, 3],
    comps := [{ kind := 0, u := [0, 2], rot := false }, { kind := 1, u := [], rot := true }] },
  { cls := [7, 15], w := [5, 6, 5, 4, 2, 3, 0, 2, 1, 3, 4, 5, 4, 3, 0, 2, 1, 3],
    comps := [{ kind := 0, u := [2, 0], rot := false }, { kind := 1, u := [], rot := true }] },
  { cls := [7, 17], w := [2, 3, 4, 5, 6, 5, 4, 3, 2, 1, 3, 4, 5, 0, 2, 1, 3],
    comps := [{ kind := 0, u := [0, 2], rot := false }, { kind := 1, u := [], rot := false }] },
  { cls := [8], w := [6, 5, 4, 3, 0, 2, 1, 3, 4, 5, 3, 0, 2, 1, 3],
    comps := [{ kind := 1, u := [], rot := false }] },
  { cls := [8, 11], w := [4, 5, 6, 5, 3, 4, 2, 3, 0, 2, 1, 3, 4, 5, 1, 3, 4, 0, 2, 1, 3],
    comps := [{ kind := 0, u := [0, 2], rot := false }, { kind := 1, u := [], rot := false }] },
  { cls := [8, 12], w := [5, 6, 5, 3, 4, 2, 3, 0, 2, 1, 3, 4, 5, 3, 4, 3, 0, 2, 1, 3],
    comps := [{ kind := 0, u := [2, 0], rot := false }, { kind := 1, u := [], rot := true }] },
  { cls := [8, 19], w := [6, 5, 4, 3, 0, 2, 1, 3, 4, 5, 3, 4, 0, 2, 3],
    comps := [{ kind := 0, u := [0, 2], rot := false }, { kind := 1, u := [], rot := true }] },
  { cls := [9], w := [2, 3, 4, 5, 2, 1, 3, 4, 2, 1, 3],
    comps := [{ kind := 0, u := [0, 2], rot := false }] },
  { cls := [9, 10], w := [2, 3, 4, 5, 6, 5, 3, 4, 2, 3, 0, 2, 1, 3, 4, 5, 1, 3, 4, 0, 2, 1, 3],
    comps := [{ kind := 0, u := [0, 2], rot := false }, { kind := 1, u := [], rot := false }] },
  { cls := [9, 11, 13, 20], w := [0, 2, 3, 4, 5, 3, 2, 0],
    comps := [{ kind := 2, u := [2, 1, 3, 4, 2, 1, 3, 1], rot := false }] },
  { cls := [9, 12, 16, 17], w := [2, 3, 4, 5, 2, 0],
    comps := [{ kind := 2, u := [2, 1, 3, 4, 2, 1, 3, 2], rot := true }] },
  { cls := [10], w := [6, 5, 4, 2, 3, 0, 2, 1, 3, 4, 5, 0, 2, 1, 3],
    comps := [{ kind := 1, u := [], rot := false }] },
  { cls := [10, 14], w := [5, 6, 5, 4, 3, 0, 2, 1, 3, 4, 5, 3, 4, 3, 0, 2, 1, 3],
    comps := [{ kind := 0, u := [2, 0], rot := false }, { kind := 1, u := [], rot := true }] },
  { cls := [10, 18], w := [4, 5, 6, 5, 4, 3, 2, 1, 3, 4, 5, 0, 2, 1, 3],
    comps := [{ kind := 0, u := [0, 2], rot := false }, { kind := 1, u := [], rot := false }] },
  { cls := [11], w := [4, 5, 2, 1, 3, 4, 2, 1, 3],
    comps := [{ kind := 0, u := [0, 2], rot := false }] },
  { cls := [11, 15, 16, 18], w := [4, 5, 2, 0],
    comps := [{ kind := 2, u := [2, 1, 3, 4, 2, 1, 3, 2], rot := true }] },
  { cls := [12], w := [5, 2, 3, 4, 1, 3],
    comps := [{ kind := 0, u := [0, 2], rot := false }] },
  { cls := [12, 14, 15, 20], w := [5, 1, 3, 2, 0],
    comps := [{ kind := 2, u := [3, 2, 1, 3, 4, 1, 3, 2], rot := true }] },
  { cls := [13], w := [3, 4, 5, 1, 3, 4, 2, 1, 3],
    comps := [{ kind := 0, u := [0, 2], rot := false }] },
  { cls := [13, 14, 16, 19], w := [3, 4, 5, 0],
    comps := [{ kind := 2, u := [2, 1, 3, 4, 2, 1, 3, 2], rot := true }] },
  { cls := [14], w := [5, 3, 4, 2, 1, 3],
    comps := [{ kind := 0, u := [0, 2], rot := false }] },
  { cls := [15], w := [5, 4, 1, 3],
    comps := [{ kind := 0, u := [0, 2], rot := false }] },
  { cls := [16], w := [4, 5, 3, 4, 2, 3],
    comps := [{ kind := 0, u := [0, 2], rot := false }] },
  { cls := [17], w := [1, 3, 4, 0, 2, 1, 3],
    comps := [{ kind := 0, u := [0, 2], rot := false }] },
  { cls := [17, 18, 19, 20], w := [],
    comps := [{ kind := 2, u := [2, 1, 3, 4, 2, 1, 3, 1], rot := false }] },
  { cls := [18], w := [4, 3, 0, 2, 1, 3],
    comps := [{ kind := 0, u := [2, 0], rot := false }] },
  { cls := [19], w := [2, 1, 3, 4, 0, 2, 3],
    comps := [{ kind := 0, u := [0, 2], rot := false }] },
  { cls := [20], w := [0, 2, 3],
    comps := [{ kind := 0, u := [0, 2], rot := false }] }]

end CertData

end CFSG.RankThree.PartOne.KE
