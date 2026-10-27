module

public import Certificates.Data.E6Order3
public import CFSG.LocalAnalysis.StandardType.GGTwE6SCFourWeylData
public import CFSG.LocalAnalysis.StandardType.GGTwE6SCFourWeylEntries

public section

namespace CFSG.StandardType.SCFourCover.WeylFix

open CFSG.Blueprint.Chevalley
open CFSG.LieType.SeitzGeneration.ExcWideThree.E6Order3 (reflIdx)

@[expose] def r3 (a k : ℕ) : ℕ := Nat.land (Nat.shiftRight roots3 (2 * (6 * a + k))) 3

@[expose] def dv (j a k : ℕ) : ℕ := (r3 a k + bif Nat.beq k j then 2 else 0) % 3

@[expose] def det3N (p q v : ℕ × ℕ) (c1 c2 c3 : ℕ) : ℕ :=
  (dv p.1 p.2 c1 * dv q.1 q.2 c2 * dv v.1 v.2 c3 + dv p.1 p.2 c2 * dv q.1 q.2 c3 * dv v.1 v.2 c1 +
    dv p.1 p.2 c3 * dv q.1 q.2 c1 * dv v.1 v.2 c2 +
    2 * (dv p.1 p.2 c1 * dv q.1 q.2 c3 * dv v.1 v.2 c2 +
      dv p.1 p.2 c2 * dv q.1 q.2 c1 * dv v.1 v.2 c3 +
      dv p.1 p.2 c3 * dv q.1 q.2 c2 * dv v.1 v.2 c1)) % 3

@[expose] def minor2N (p q : ℕ × ℕ) (c1 c2 : ℕ) : ℕ :=
  (dv p.1 p.2 c1 * dv q.1 q.2 c2 + 2 * (dv p.1 p.2 c2 * dv q.1 q.2 c1)) % 3

@[expose] def pairsOf {α : Type} : List α → List (α × α)
  | [] => []
  | x :: xs => xs.map (fun y => (x, y)) ++ pairsOf xs

@[expose] def cols2 : List (ℕ × ℕ) :=
  [(0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (1, 2), (1, 3), (1, 4), (1, 5), (2, 3), (2, 4),
    (2, 5), (3, 4), (3, 5), (4, 5)]

@[expose] def basisOf (olds : List (ℕ × ℕ)) : Option ((ℕ × ℕ) × (ℕ × ℕ) × ℕ × ℕ) :=
  (pairsOf olds).findSome? fun pq =>
    (cols2.find? fun c => minor2N pq.1 pq.2 c.1 c.2 != 0).map fun c => (pq.1, pq.2, c.1, c.2)

@[expose] def prune (olds : List (ℕ × ℕ)) (v : ℕ × ℕ) : Bool :=
  match basisOf olds with
  | none => false
  | some (p, q, c1, c2) => (List.range 6).any fun c3 => det3N p q v c1 c2 c3 != 0

@[expose] def orthB (r s : ℕ) : Bool := Nat.testBit orthMask (72 * r + s)

@[expose] def wTest (t : List ℕ) : Bool :=
  (List.range 6).all fun i =>
    (r3 (t.getD 0 0) i + 2 * r3 (t.getD 2 0) i + r3 (t.getD 4 0) i + 2 * r3 (t.getD 5 0) i) % 3 ==
      [1, 0, 2, 0, 1, 2].getD i 0

@[expose] def leavesFrom (a0 : ℕ) : List (List ℕ) :=
  (adjRoots.getD a0 []).flatMap fun a2 =>
  (adjRoots.getD a2 []).flatMap fun a3 =>
    bif orthB a3 a0 && !prune [(0, a0), (2, a2)] (3, a3) then
    (adjRoots.getD a3 []).flatMap fun a4 =>
      bif orthB a4 a0 && orthB a4 a2 && !prune [(0, a0), (2, a2), (3, a3)] (4, a4) then
      (adjRoots.getD a4 []).flatMap fun a5 =>
        bif orthB a5 a0 && orthB a5 a2 && orthB a5 a3 &&
          !prune [(0, a0), (2, a2), (3, a3), (4, a4)] (5, a5) then
        (adjRoots.getD a3 []).flatMap fun a1 =>
          bif orthB a1 a0 && orthB a1 a2 && orthB a1 a4 && orthB a1 a5 &&
            !prune [(0, a0), (2, a2), (3, a3), (4, a4), (5, a5)] (1, a1) &&
            wTest [a0, a1, a2, a3, a4, a5] then [[a0, a1, a2, a3, a4, a5]] else []
        else []
      else []
    else []

@[expose] def tupleOf (rs : List ℕ) : List ℕ :=
  rs.foldr (fun b t => t.map (reflIdx 72 b)) (List.range 6)

@[expose] def comb (t : List ℕ) (c k : ℕ) : ℕ :=
  c % 3 * dv 0 (t.getD 0 0) k + c / 3 % 3 * dv 1 (t.getD 1 0) k +
    c / 9 % 3 * dv 2 (t.getD 2 0) k + c / 27 % 3 * dv 3 (t.getD 3 0) k +
    c / 81 % 3 * dv 4 (t.getD 4 0) k + c / 243 % 3 * dv 5 (t.getD 5 0) k

@[expose] def coefOK (t : List ℕ) (p : ℕ × ℕ) : Bool :=
  (List.range 6).all fun k => (comb t p.2 k + 2 * r3 p.1 k) % 3 == 0

@[expose] def entryOK (t : List ℕ) (e : List (ℕ × ℕ)) : Bool :=
  tupleOf (e.map Prod.fst) == t && e.all fun p => decide (p.1 < 72) && coefOK t p

@[expose] def allPairs {α β : Type} (p : α → β → Bool) : List α → List β → Bool
  | [], [] => true
  | a :: as, b :: bs => p a b && allPairs p as bs
  | _, _ => false

@[expose] def searchOK (l0 : List ℕ) : Bool :=
  l0.all fun a0 => allPairs entryOK (leavesFrom a0) (entriesAt.getD a0 [])

@[expose] def gram3 (r s : ℕ) : ℕ :=
  (2 * (r3 r 0 * r3 s 0 + r3 r 1 * r3 s 1 + r3 r 2 * r3 s 2 + r3 r 3 * r3 s 3 +
    r3 r 4 * r3 s 4 + r3 r 5 * r3 s 5 + r3 r 0 * r3 s 2 + r3 r 2 * r3 s 0 + r3 r 1 * r3 s 3 +
    r3 r 3 * r3 s 1 + r3 r 2 * r3 s 3 + r3 r 3 * r3 s 2 + r3 r 3 * r3 s 4 + r3 r 4 * r3 s 3 +
    r3 r 4 * r3 s 5 + r3 r 5 * r3 s 4)) % 3

@[expose] def roots3OK : Bool :=
  (List.range 72).all fun a => (List.range 6).all fun k =>
    r3 a k == (e6Certificate.roots.getD a 0 / 16 ^ k % 16 + 1) % 3

@[expose] def adjOK : Bool :=
  (List.range 72).all fun r => (List.range 72).all fun s =>
    gram3 r s != 2 || r == s || (adjRoots.getD r []).contains s

@[expose] def orthOK : Bool :=
  (List.range 72).all fun r => (List.range 72).all fun s => gram3 r s != 0 || orthB r s

theorem roots3OK_eq : roots3OK = true := by decide +kernel

theorem adjOK_eq : adjOK = true := by decide +kernel

theorem orthOK_eq : orthOK = true := by decide +kernel

theorem searchOK_0 : searchOK (List.range' 0 18) = true := by decide +kernel

theorem searchOK_1 : searchOK (List.range' 18 18) = true := by decide +kernel

theorem searchOK_2 : searchOK (List.range' 36 18) = true := by decide +kernel

theorem searchOK_3 : searchOK (List.range' 54 18) = true := by decide +kernel

end CFSG.StandardType.SCFourCover.WeylFix

end
