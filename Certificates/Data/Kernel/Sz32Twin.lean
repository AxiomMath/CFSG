module

public import Init

public section

namespace CFSG.KC.Sz32T

@[expose] def letN {α : Sort _} (x : Nat) (f : Nat → α) : α :=
  Nat.rec (motive := fun _ => α) (f 0) (fun n _ => f (n + 1)) x

@[expose] def fa (x y : Nat) : Nat := (x % 32) ^^^ (y % 32)

@[expose] def clT (a b s : Nat) : Nat := cond (Nat.beq ((b >>> s) % 2) 0) 0 (a <<< s)

@[expose] def clmul (a b : Nat) : Nat :=
  clT a b 0 ^^^ clT a b 1 ^^^ clT a b 2 ^^^ clT a b 3 ^^^ clT a b 4

@[expose] def redT (s p : Nat) : Nat :=
  letN p fun p => cond (Nat.beq ((p >>> (5 + s)) % 2) 0) p (p ^^^ (37 <<< s))

@[expose] def fm (x y : Nat) : Nat :=
  letN (x % 32) fun a => letN (y % 32) fun b => redT 0 (redT 1 (redT 2 (redT 3 (clmul a b))))

@[expose] def fpow (x : Nat) : Nat → Nat
  | 0 => 1
  | n + 1 => fm (fpow x n) x

@[expose] def eq32 (x y : Nat) : Bool := x % 32 == y % 32

@[expose] def ent (M i : Nat) : Nat := M / 32 ^ i % 32

@[expose] def packL : List Nat → Nat
  | [] => 0
  | a :: l => a % 32 + 32 * packL l

@[expose] def mvE (A v i : Nat) : Nat :=
  fa (fa (fa (fm (ent A (4 * i)) (ent v 0)) (fm (ent A (4 * i + 1)) (ent v 1)))
    (fm (ent A (4 * i + 2)) (ent v 2))) (fm (ent A (4 * i + 3)) (ent v 3))

@[expose] def mv (A v : Nat) : Nat :=
  letN A fun A => letN v fun v => packL [mvE A v 0, mvE A v 1, mvE A v 2, mvE A v 3]

@[expose] def mmE (A B i j : Nat) : Nat :=
  fa (fa (fa (fm (ent A (4 * i)) (ent B j)) (fm (ent A (4 * i + 1)) (ent B (4 + j))))
    (fm (ent A (4 * i + 2)) (ent B (8 + j)))) (fm (ent A (4 * i + 3)) (ent B (12 + j)))

@[expose] def mm (A B : Nat) : Nat :=
  letN A fun A => letN B fun B => packL [mmE A B 0 0, mmE A B 0 1, mmE A B 0 2, mmE A B 0 3, mmE A B 1 0, mmE A B 1 1,
    mmE A B 1 2, mmE A B 1 3, mmE A B 2 0, mmE A B 2 1, mmE A B 2 2, mmE A B 2 3,
    mmE A B 3 0, mmE A B 3 1, mmE A B 3 2, mmE A B 3 3]

@[expose] def polyE (I T1 T2 T3 c i : Nat) : Nat :=
  fa (fa (fa (fm (ent c 0) (ent I i)) (fm (ent c 1) (ent T1 i))) (fm (ent c 2) (ent T2 i)))
    (fm (ent c 3) (ent T3 i))

@[expose] def polyG (I T1 T2 T3 c : Nat) : Nat :=
  letN c fun c => packL [polyE I T1 T2 T3 c 0, polyE I T1 T2 T3 c 1, polyE I T1 T2 T3 c 2,
    polyE I T1 T2 T3 c 3, polyE I T1 T2 T3 c 4, polyE I T1 T2 T3 c 5, polyE I T1 T2 T3 c 6,
    polyE I T1 T2 T3 c 7, polyE I T1 T2 T3 c 8, polyE I T1 T2 T3 c 9, polyE I T1 T2 T3 c 10,
    polyE I T1 T2 T3 c 11, polyE I T1 T2 T3 c 12, polyE I T1 T2 T3 c 13, polyE I T1 T2 T3 c 14,
    polyE I T1 T2 T3 c 15]

@[expose] def allLt : Nat → (Nat → Bool) → Bool
  | 0, _ => true
  | n + 1, f => allLt n f && f n

@[expose] def onB (y0 y1 y2 y3 : Nat) : Bool :=
  if y0 % 32 = 0 then y1 % 32 == 0 && y2 % 32 == 0 && y3 % 32 != 0
  else eq32 (fm y3 (fpow y0 9))
    (fa (fa (fpow y1 10) (fm (fm y1 y2) (fpow y0 8))) (fm (fpow y2 8) (fpow y0 2)))

@[expose] def onV (y : Nat) : Bool := letN y fun y => onB (ent y 0) (ent y 1) (ent y 2) (ent y 3)

@[expose] def smulEq (P l G : Nat) : Bool :=
  letN P fun P => letN l fun l => letN G fun G =>
    allLt 16 fun i => eq32 (ent P i) (fm l (ent G i))

@[expose] def g0N : Nat := 1152956690054807629

@[expose] def idN : Nat := 37778932988857102106625

@[expose] def t1N : Nat := 1165372896630396444708025

@[expose] def t2N : Nat := 419754637832814652278701

@[expose] def t3N : Nat := 526008823823803755250795

@[expose] def bInvN : Nat := 691384881691354192149217

@[expose] def paN : Nat := 32801

@[expose] def pbN : Nat := 557121

@[expose] def gTab : List Nat :=
  [37778932988857102106625, 1152956690054807629, 37867707946979733965662,
    494481188059851549272958, 1165094992859475942009967, 1165372896630396444708025,
    570439176955986505930369, 951115484409522830758137, 61678594755849562659947,
    952861082631661161909807, 419754637832814652278701, 587839579418911919502699,
    525782850322460944215403, 428973668639089175670701, 429640057922499865146927,
    526008823823803755250795, 586878042749033583578361, 419397232084677150154369,
    953476743086251309060281, 61604807671730778444911, 950504435781692433076094,
    571256598116584490233694, 1166238740108281874704461, 1164153055363712076384257,
    493488522474162015469568]

@[expose] def gAt (k : Nat) : Nat := gTab.getD k 0

@[expose] def chainOk : Bool :=
  Nat.beq (gAt 0) idN && allLt 24 fun k => Nat.beq (gAt (k + 1)) (mm (gAt k) g0N)

@[expose] def polyT (w : Nat) : Nat := polyG idN t1N t2N t3N (mv bInvN w)

@[expose] def wOkP (P : Nat) (kl : Nat × Nat) : Bool :=
  !onV (mv P paN) || !onV (mv P pbN) || (Nat.blt kl.1 25 && smulEq P kl.2 (gAt kl.1))

@[expose] def wOk (w : Nat) (kl : Nat × Nat) : Bool := letN (polyT w) fun P => wOkP P kl

@[expose] def look : List (Nat × Nat × Nat) → Nat → Nat × Nat
  | [], _ => (25, 0)
  | (i, k, l) :: r, n => if i = n then (k, l) else look r n

@[expose] def wits : List (Nat × Nat × Nat) :=
  [(0, 0, 1), (2, 23, 1), (33, 12, 16), (35, 11, 16), (117, 14, 13), (119, 9, 13), (252, 18, 10),
    (254, 5, 10), (324, 10, 15), (326, 13, 15), (505, 20, 20), (507, 3, 20), (636, 7, 10),
    (638, 16, 10), (645, 6, 1), (647, 17, 1), (701, 15, 16), (703, 8, 16), (764, 19, 13),
    (766, 4, 13), (877, 2, 20), (879, 21, 20), (960, 1, 15), (962, 22, 15), (1024, 24, 1)]

@[expose] def nT (x y : Nat) : Nat := fa (fa (fpow x 10) (fm x y)) (fpow y 8)

@[expose] def lineW (x y : Nat) : Nat := packL [1, x, y, nT x y]

@[expose] def inftyW : Nat := packL [0, 0, 0, 1]

@[expose] def lineOk (ws : List (Nat × Nat × Nat)) (x y : Nat) : Bool :=
  wOk (lineW x y) (look ws (32 * x + y))

@[expose] def rowsOk (ws : List (Nat × Nat × Nat)) (j : Nat) : Bool :=
  allLt 4 fun d => allLt 32 fun y => lineOk ws (4 * j + d) y

@[expose] def inftyOk (ws : List (Nat × Nat × Nat)) : Bool := wOk inftyW (look ws 1024)

end CFSG.KC.Sz32T

end
