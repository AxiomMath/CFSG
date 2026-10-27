module

public import CFSG.Certificates.Kernel.Enum.Defs

public section

namespace CFSG.KC.S63K

open CFSG.KC.Enum

@[expose] noncomputable def ptsOKF (P : Nat → Nat) : Bool :=
  allN 2457 fun v =>
    decide (P (3 * v) < P (3 * v + 1)) && decide (P (3 * v + 1) < P (3 * v + 2)) &&
      decide (P (3 * v + 2) < 819)

@[expose] noncomputable def onLineF (P : Nat → Nat) (p v : Nat) : Bool :=
  P (3 * v) == p || P (3 * v + 1) == p || P (3 * v + 2) == p

@[expose] noncomputable def incOKF (P L : Nat → Nat) : Bool :=
  (allN 819 fun x => allN 9 fun k =>
      decide (L (9 * x + k) < 2457) && onLineF P x (L (9 * x + k))) &&
    (allN 2457 fun v => allN 3 fun k =>
      (List.range 9).any fun j => L (9 * P (3 * v + k) + j) == v)

@[expose] noncomputable def meetOKF (P L : Nat → Nat) : Bool :=
  allN 819 fun x => allN 9 fun i => allN 9 fun j => i == j || allN 3 fun a => allN 3 fun b =>
    P (3 * L (9 * x + i) + a) == x || P (3 * L (9 * x + j) + b) == x ||
      P (3 * L (9 * x + i) + a) != P (3 * L (9 * x + j) + b)

@[expose] noncomputable def nbrF (P L : Nat → Nat) (x : Nat) : List Nat :=
  if x < 819 then (List.range 9).map fun k => L (9 * x + k) + 819
  else (List.range 3).map fun k => P (3 * (x - 819) + k)

@[expose] noncomputable def layOKF (P L : Nat → Nat) (b : Nat) (lay par : Nat → Nat) : Bool :=
  decide (b < 3276) && lay b == 0 && allN 3276 fun x =>
    decide (lay x ≤ 6) &&
    (x == b || (decide (par x < 3276) && (nbrF P L x).contains (par x) &&
      lay (par x) + 1 == lay x)) &&
    (nbrF P L x).all (fun y => decide (lay y ≤ lay x + 1)) &&
    (lay x == 0 || decide (5 < lay x) ||
      (nbrF P L x).all fun y => lay y + 1 != lay x || y == par x)

@[expose] noncomputable def lineMapsF (P g : Nat → Nat) (v w : Nat) : Bool :=
  (List.range 3).all fun k => onLineF P (g (P (3 * v + k))) w

@[expose] noncomputable def actOKF (P g : Nat → Nat) (y x : Nat) : Bool :=
  if y < 819 then decide (x < 819) && g y == x
  else decide (819 ≤ x) && decide (x < 3276) && lineMapsF P g (y - 819) (x - 819)

@[expose] noncomputable def sortKeyF (a b c : Nat) : Nat :=
  let p := if a ≤ b then (a, b) else (b, a)
  let q := if p.2 ≤ c then (p.2, c) else (c, p.2)
  let r := if p.1 ≤ q.1 then (p.1, q.1) else (q.1, p.1)
  (r.1 * 819 + r.2) * 819 + q.2

@[expose] noncomputable def keyF (P : Nat → Nat) (v : Nat) : Nat :=
  (P (3 * v) * 819 + P (3 * v + 1)) * 819 + P (3 * v + 2)

@[expose] noncomputable def actSOKF (P g : Nat → Nat) (x y : Nat) : Bool :=
  if x < 819 then g x == y
  else decide (819 ≤ y) && decide (y < 3276) &&
    sortKeyF (g (P (3 * (x - 819)))) (g (P (3 * (x - 819) + 1))) (g (P (3 * (x - 819) + 2))) ==
      keyF P (y - 819)

@[expose] noncomputable def orbActF (P : Nat → Nat) (g : Nat → Nat → Nat) (k cnt : Nat)
    (O W : Nat → Nat) : Bool :=
  allN cnt fun h => allN k fun j =>
    decide (W (k * h + j) < cnt) && actSOKF P (g j) (O h) (O (W (k * h + j)))

@[expose] noncomputable def orbOKRF (N k : Nat) (act : Nat → Nat → Nat → Bool) (root cnt : Nat)
    (items : Nat → Bool) (O Pa La Ps : Nat → Nat) : Bool :=
  O 0 == root && (allN cnt fun i => decide (O i < N)) &&
    (allN cnt fun i => i == 0 || (decide (Pa i < i) && decide (La i < k) &&
      act (La i) (O (Pa i)) (O i))) &&
    allN N fun x => !items x || (decide (Ps x < cnt) && O (Ps x) == x)

@[expose] noncomputable def cycF (lay par : Nat → Nat) (nb : Nat → List Nat) : List Nat :=
  let q := (List.find? (fun x => lay x == 6) (List.range 3276)).getD 0
  let ps := List.filter (fun y => lay y == 5) (nb q)
  let p1 := ps[0]!
  let p2 := ps[1]!
  let back := fun y => List.foldl (fun acc _ => par acc.head! :: acc) [y] (List.range 5)
  back p1 ++ [q] ++ (back p2).tail!.reverse

@[expose] noncomputable def cycleOKF (P L : Nat → Nat) (c : Nat → Nat) : Bool :=
  allN 12 fun i =>
    decide (c i < 3276) && (nbrF P L (c i)).contains (c ((i + 1) % 12)) && c i != c ((i + 2) % 12)

end CFSG.KC.S63K

end
