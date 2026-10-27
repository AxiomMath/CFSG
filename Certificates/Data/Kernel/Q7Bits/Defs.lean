module

public import CFSG.ClassicalInvolution.Phan.PhanS19Q7Inputs

public section

namespace CFSG.Certificates.Kernel.Q7Bits

open CFSG.ClassicalInvolution.PhanB3.S.Std.Q7

@[expose] def NL : Nat := 120100

@[expose] def MM : Nat := 2 ^ (NL + 64) - 1

@[expose] def forceN {β : Sort _} (y : Nat) (k : Nat → β) : β :=
  bif Nat.beq y 0 then k 0 else k y

@[expose] def mix (i : Nat) : Nat := i * 11400714819323198485 % 18446744073709551616

structure P3 where
  b0 : Nat
  b1 : Nat
  b2 : Nat

@[expose] def z3 : P3 := ⟨0, 0, 0⟩

structure P6 where
  re : P3
  im : P3

@[expose] def z6 : P6 := ⟨z3, z3⟩

structure Tb where
  r : List P3
  i : List P3

@[expose] def laddK {β : Sort _} (x y : P3) (k : P3 → β) : β :=
  forceN (Nat.xor x.b0 y.b0) fun s0 => forceN (Nat.land x.b0 y.b0) fun c0 =>
  forceN (Nat.xor x.b1 y.b1) fun t1 => forceN (Nat.xor t1 c0) fun s1 =>
  forceN (Nat.lor (Nat.land x.b1 y.b1) (Nat.land c0 t1)) fun c1 =>
  forceN (Nat.xor x.b2 y.b2) fun t2 => forceN (Nat.xor t2 c1) fun s2 =>
  forceN (Nat.lor (Nat.land x.b2 y.b2) (Nat.land c1 t2)) fun c2 =>
  forceN (Nat.land s0 c2) fun k0 => forceN (Nat.land s1 k0) fun k1 =>
  forceN (Nat.xor s0 c2) fun r0 => forceN (Nat.xor s1 k0) fun r1 =>
  forceN (Nat.xor s2 k1) fun r2 => k ⟨r0, r1, r2⟩

@[expose] def orO {β : Sort _} : Option Nat → Bool → Nat → (Option Nat → β) → β
  | none, b, q, k => bif b then k (some q) else k none
  | some a, b, q, k => bif b then forceN (Nat.lor a q) fun a => k (some a) else k (some a)

@[expose] def selK {β : Sort _} (t : Nat → Nat) (j q0 q1 q2 q3 q4 q5 q6 q7 : Nat) (k : Nat → β) :
    β :=
  orO none ((t 0).testBit j) q0 fun a => orO a ((t 1).testBit j) q1 fun a =>
  orO a ((t 2).testBit j) q2 fun a => orO a ((t 3).testBit j) q3 fun a =>
  orO a ((t 4).testBit j) q4 fun a => orO a ((t 5).testBit j) q5 fun a =>
  orO a ((t 6).testBit j) q6 fun a => orO a ((t 0).testBit j) q7 fun a => k (a.getD 0)

@[expose] def lmapK {β : Sort _} (m : Nat) (x : P3) (t : Nat → Nat) (k : P3 → β) : β :=
  forceN (Nat.xor x.b0 m) fun n0 => forceN (Nat.xor x.b1 m) fun n1 =>
  forceN (Nat.xor x.b2 m) fun n2 =>
  forceN (Nat.land n0 n1) fun a0 => forceN (Nat.land x.b0 n1) fun a1 =>
  forceN (Nat.land n0 x.b1) fun a2 => forceN (Nat.land x.b0 x.b1) fun a3 =>
  forceN (Nat.land a0 n2) fun q0 => forceN (Nat.land a1 n2) fun q1 =>
  forceN (Nat.land a2 n2) fun q2 => forceN (Nat.land a3 n2) fun q3 =>
  forceN (Nat.land a0 x.b2) fun q4 => forceN (Nat.land a1 x.b2) fun q5 =>
  forceN (Nat.land a2 x.b2) fun q6 => forceN (Nat.land a3 x.b2) fun q7 =>
  selK t 0 q0 q1 q2 q3 q4 q5 q6 q7 fun r0 => selK t 1 q0 q1 q2 q3 q4 q5 q6 q7 fun r1 =>
  selK t 2 q0 q1 q2 q3 q4 q5 q6 q7 fun r2 => k ⟨r0, r1, r2⟩

@[expose] def lzero (m : Nat) (x : P3) : Nat :=
  Nat.xor (Nat.lor (Nat.xor x.b0 x.b1) (Nat.xor x.b1 x.b2)) m

@[expose] def sumAK {β : Sort _} : P3 → List P3 → (P3 → β) → β
  | a, [], k => k a
  | a, x :: l, k => laddK a x fun a => sumAK a l k

@[expose] def sumK {β : Sort _} : List P3 → (P3 → β) → β
  | [], k => k z3
  | x :: l, k => sumAK x l k

@[expose] def tblAK {β : Sort _} (m : Nat) (x : P3) : List Nat → (List P3 → β) → β
  | [], k => k []
  | j :: js, k => lmapK m x (fun v => j * v % 7) fun y => tblAK m x js fun l => k (y :: l)

@[expose] def tblK {β : Sort _} (m : Nat) (x : P3) (k : List P3 → β) : β :=
  tblAK m x [2, 3, 4, 5, 6] fun l => k (z3 :: x :: l)

@[expose] def tbPK {β : Sort _} (m : Nat) (x : P6) (k : Tb → β) : β :=
  tblK m x.re fun r => tblK m x.im fun i => k ⟨r, i⟩

@[expose] def sel : List P3 → Nat → P3
  | [], _ => z3
  | x :: l, i => bif Nat.beq i 0 then x else sel l (i - 1)

@[expose] def addO {β : Sort _} (a : Option P3) (l : List P3) (i : Nat) (k : Option P3 → β) : β :=
  bif Nat.beq i 0 then k a else
    match a with
    | none => k (some (sel l i))
    | some a => laddK a (sel l i) fun a => k (some a)

@[expose] def linAK {β : Sort _} : Option P3 → Option P3 → List (Tb × Nat) → (P6 → β) → β
  | r, i, [], k => k ⟨r.getD z3, i.getD z3⟩
  | r, i, (t, a) :: l, k => forceN (a % 7) fun p => forceN (a / 7 % 7) fun q =>
    addO r t.r p fun r => addO r t.i ((7 - q) % 7) fun r => addO i t.r q fun i =>
    addO i t.i p fun i => linAK r i l k

@[expose] def linK {β : Sort _} (l : List (Tb × Nat)) (k : P6 → β) : β := linAK none none l k

@[expose] def linCAK {β : Sort _} : Option P3 → Option P3 → List (Tb × Nat) → (P6 → β) → β
  | r, i, [], k => k ⟨r.getD z3, i.getD z3⟩
  | r, i, (t, a) :: l, k => forceN (a % 7) fun p => forceN (a / 7 % 7) fun q =>
    addO r t.r p fun r => addO r t.i q fun r => addO i t.r q fun i =>
    addO i t.i ((7 - p) % 7) fun i => linCAK r i l k

@[expose] def linCK {β : Sort _} (l : List (Tb × Nat)) (k : P6 → β) : β := linCAK none none l k

@[expose] def nsqK {β : Sort _} (m : Nat) (x : P6) (k : List P3 → β) : β :=
  lmapK m x.re (fun v => (7 - v * v % 7) % 7) fun a =>
    lmapK m x.im (fun v => (7 - v * v % 7) % 7) fun b => k [a, b]

@[expose] def sqsK {β : Sort _} (m s : Nat) (x : P6) (k : List P3 → β) : β :=
  lmapK m x.re (fun v => s * (v * v) % 7) fun a =>
    lmapK m x.im (fun v => s * (v * v) % 7) fun b => k [a, b]

@[expose] def tabK {β : Sort _} (f : Nat → Nat) : Nat → Nat → P6 → (P6 → β) → β
  | _, 0, acc, k => k acc
  | i, n + 1, acc, k => forceN (i + 1) fun i' => forceN (f i) fun v => forceN (2 ^ (i + 64)) fun e =>
    forceN (Nat.xor (Nat.lor acc.re.b0 (bif (v % 7).testBit 0 then e else 0)) (mix (6 * i)))
      fun a0 =>
    forceN (Nat.xor (Nat.lor acc.re.b1 (bif (v % 7).testBit 1 then e else 0)) (mix (6 * i + 1)))
      fun a1 =>
    forceN (Nat.xor (Nat.lor acc.re.b2 (bif (v % 7).testBit 2 then e else 0)) (mix (6 * i + 2)))
      fun a2 =>
    forceN (Nat.xor (Nat.lor acc.im.b0 (bif (v / 7).testBit 0 then e else 0)) (mix (6 * i + 3)))
      fun a3 =>
    forceN (Nat.xor (Nat.lor acc.im.b1 (bif (v / 7).testBit 1 then e else 0)) (mix (6 * i + 4)))
      fun a4 =>
    forceN (Nat.xor (Nat.lor acc.im.b2 (bif (v / 7).testBit 2 then e else 0)) (mix (6 * i + 5)))
      fun a5 =>
      tabK f i' n ⟨⟨a0, a1, a2⟩, ⟨a3, a4, a5⟩⟩ k

@[expose] def rep (p w : Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => Nat.xor (Nat.lor (rep p w n) ((p >>> 64) <<< (w * n + 64))) (mix n)

@[expose] def spread (p w : Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => Nat.xor (Nat.lor (spread p w n)
      (bif p.testBit (n + 64) then (2 ^ w - 1) <<< (w * n + 64) else 0)) (mix n)

@[expose] def mapP (g : Nat → Nat) (s : Nat) (x : P6) : P6 :=
  ⟨⟨Nat.xor (g x.re.b0) (mix s), Nat.xor (g x.re.b1) (mix (s + 1)),
      Nat.xor (g x.re.b2) (mix (s + 2))⟩,
    ⟨Nat.xor (g x.im.b0) (mix (s + 3)), Nat.xor (g x.im.b1) (mix (s + 4)),
      Nat.xor (g x.im.b2) (mix (s + 5))⟩⟩

@[expose] def forceP6 {β : Sort _} (x : P6) (k : P6 → β) : β :=
  forceN x.re.b0 fun a => forceN x.re.b1 fun b => forceN x.re.b2 fun c =>
  forceN x.im.b0 fun d => forceN x.im.b1 fun e => forceN x.im.b2 fun f => k ⟨⟨a, b, c⟩, ⟨d, e, f⟩⟩

@[expose] def join1 (a b c d : Nat) : Nat :=
  Nat.lor (Nat.lor (Nat.lor a ((b >>> 64) <<< (117649 + 64))) ((c >>> 64) <<< (120050 + 64)))
    ((d >>> 64) <<< (120099 + 64))

@[expose] def joinP (a b c d : P6) : P6 :=
  ⟨⟨join1 a.re.b0 b.re.b0 c.re.b0 d.re.b0, join1 a.re.b1 b.re.b1 c.re.b1 d.re.b1,
      join1 a.re.b2 b.re.b2 c.re.b2 d.re.b2⟩,
    ⟨join1 a.im.b0 b.im.b0 c.im.b0 d.im.b0, join1 a.im.b1 b.im.b1 c.im.b1 d.im.b1,
      join1 a.im.b2 b.im.b2 c.im.b2 d.im.b2⟩⟩

@[expose] def constB (v j n s : Nat) : Nat :=
  Nat.xor (bif v.testBit j then (2 ^ n - 1) <<< 64 else 0) (mix s)

@[expose] def constP (a n s : Nat) : P6 :=
  ⟨⟨constB (a % 7) 0 n s, constB (a % 7) 1 n (s + 1), constB (a % 7) 2 n (s + 2)⟩,
    ⟨constB (a / 7) 0 n (s + 3), constB (a / 7) 1 n (s + 4), constB (a / 7) 2 n (s + 5)⟩⟩

@[expose] def coordsK {β : Sort _} (id sq np : P6) (k : P6 → P6 → P6 → P6 → P6 → β) : β :=
  forceP6 (joinP (constP 1 117649 0) z6 z6 z6) fun u1 =>
  forceP6 (joinP (mapP (fun p => spread p 2401 49) 6 id) (constP 1 2401 12) z6 z6) fun u2 =>
  forceP6 (mapP (fun p => spread p 49 2401) 18 np) fun a =>
  forceP6 (mapP (fun p => rep p 49 2401) 24 sq) fun b =>
  laddK a.re b.re fun abr => laddK a.im b.im fun abi =>
  forceP6 (joinP ⟨abr, abi⟩ (mapP (fun p => spread p 49 49) 30 id) (constP 1 49 36) z6) fun u4 =>
  forceP6 (joinP (mapP (fun p => rep (spread p 49 49) 2401 49) 42 id)
    (mapP (fun p => rep p 49 49) 48 sq) id (constP 1 1 54)) fun u5 =>
  forceP6 (joinP (mapP (fun p => rep p 49 2401) 60 id) (mapP (fun p => rep p 49 49) 66 id) z6 z6)
    fun u6 => k u1 u2 u4 u5 u6

@[expose] def withU {β : Sort _} (k : P6 → P6 → P6 → P6 → P6 → β) : β :=
  tabK (fun k => k) 0 49 z6 fun id => tabK (fun k => gfMul k k) 0 49 z6 fun sq =>
  tabK (fun k => gfNeg (gfMul (k / 49) (k % 49))) 0 2401 z6 fun np => coordsK id sq np k

@[expose] def laneArgs (L : Nat) : Nat × Nat × Nat × Nat × Nat :=
  if L < 117649 then
    (1, L / 2401, gfAdd (gfNeg (gfMul (L / 2401) (L / 49 % 49))) (gfMul (L % 49) (L % 49)),
      L / 49 % 49, L % 49)
  else if L < 120050 then
    (0, 1, (L - 117649) / 49, gfMul ((L - 117649) % 49) ((L - 117649) % 49), (L - 117649) % 49)
  else if L < 120099 then (0, 0, 1, L - 120050, 0)
  else (0, 0, 0, 1, 0)

@[expose] def laneVec (c : N7) (L : Nat) : N7 :=
  candN c (laneArgs L).1 (laneArgs L).2.1 (laneArgs L).2.2.1 (laneArgs L).2.2.2.1
    (laneArgs L).2.2.2.2

@[expose] def forceV7 {β : Sort _} (v : N7) (k : N7 → β) : β :=
  forceN v.x0 fun a => forceN v.x1 fun b => forceN v.x2 fun c => forceN v.x3 fun d =>
  forceN v.x4 fun e => forceN v.x5 fun f => forceN v.x6 fun g => k ⟨a, b, c, d, e, f, g⟩

@[expose] def laneVecK {β : Sort _} (c : N7) (L : Nat) (k : N7 → β) : β :=
  let a := laneArgs L
  forceN a.1 fun b1 => forceN a.2.1 fun b2 => forceN a.2.2.1 fun b4 => forceN a.2.2.2.1 fun b5 =>
  forceN a.2.2.2.2 fun b6 => forceV7 (candN c b1 b2 b4 b5 b6) k

structure Tabs where
  t0 : Tb
  t1 : Tb
  t2 : Tb
  t4 : Tb
  t5 : Tb
  t6 : Tb
  th : List P3

@[expose] def bfCoef (T : Tabs) (v : N7) : List (Tb × Nat) :=
  [(T.t0, v.x3), (T.t1, v.x4), (T.t2, v.x5), (T.t4, v.x1), (T.t5, v.x2),
    (T.t6, gfMul gfKappa v.x6)]

@[expose] def herCoef (T : Tabs) (v : N7) : List (Tb × Nat) :=
  [(T.t0, gfConj v.x0), (T.t1, gfConj v.x1), (T.t2, gfConj v.x2), (T.t4, gfConj v.x4),
    (T.t5, gfConj v.x5), (T.t6, gfMul gfKappa (gfConj v.x6))]

@[expose] def adjMK {β : Sort _} (m : Nat) (T : Tabs) (v : N7) (k : Nat → β) : β :=
  linK (bfCoef T v) fun b => forceN (Nat.land (lzero m b.re) (lzero m b.im)) fun zb =>
  linK (herCoef T v) fun h => nsqK m h fun nh => forceN (herN v v % 7) fun hv =>
  addO none T.th hv fun d => sumK (d.toList ++ nh) fun d =>
    forceN (Nat.land (Nat.xor (lzero m d) m) zb) k

@[expose] def stepL (m : Nat) (T : Tabs) (V S : Nat) (c : N7) : List Nat → Nat → Option Nat
  | [], a => some a
  | L :: Ls, a =>
    bif S.testBit (L + 64) && decide (L < NL) then
      laneVecK c L fun v => adjMK m T v fun x =>
        forceN (Nat.xor (Nat.lor a (Nat.land V x)) (mix L)) fun a => stepL m T V S c Ls a
    else none

@[expose] def runLv (m : Nat) (T : Tabs) (V : Nat) (c : N7) : Nat → List (List Nat) → Option Nat
  | S, [] => some S
  | S, Ls :: rest =>
    match stepL m T V S c Ls S with
    | none => none
    | some S' => forceN S' fun S' => runLv m T V c S' rest

@[expose] def b0Coef (t1 t2 t4 t5 t6 : Tb) (c : N7) : List (Tb × Nat) :=
  [(t4, gfNeg c.x1), (t5, gfNeg c.x2), (t1, gfNeg c.x4), (t2, gfNeg c.x5),
    (t6, gfNeg (gfMul gfKappa c.x6))]

@[expose] def hcCoef (T : Tabs) (c : N7) : List (Tb × Nat) :=
  [(T.t0, c.x0), (T.t1, c.x1), (T.t2, c.x2), (T.t4, c.x4), (T.t5, c.x5),
    (T.t6, gfMul gfKappa c.x6)]

@[expose] def vtxMK {β : Sort _} (m : Nat) (T : Tabs) (u0 : P6) (h : P3) (c : N7)
    (k : Nat → β) : β :=
  nsqK m u0 fun n0 => sumK (h :: n0) fun d2 => linCK (hcCoef T c) fun hc => nsqK m hc fun nc =>
  forceN (herN c c % 7) fun g => addO none T.th g fun gh => sumK (gh.toList ++ nc) fun d3 =>
    forceN (Nat.land (Nat.land (Nat.xor (lzero m h) m) (Nat.xor (lzero m d2) m))
      (Nat.xor (lzero m d3) m)) k

@[expose] def herUUK {β : Sort _} (m : Nat) (u0 u1 u2 u4 u5 u6 : P6) (k : P3 → β) : β :=
  sqsK m 1 u0 fun a0 => sqsK m 1 u1 fun a1 => sqsK m 1 u2 fun a2 => sqsK m 1 u4 fun a4 =>
  sqsK m 1 u5 fun a5 => sqsK m gfKappa u6 fun a6 => sumK (a0 ++ a1 ++ a2 ++ a4 ++ a5 ++ a6) k

@[expose] def rowCore (c : N7) (rootL : Nat) (lvls : List (List Nat)) : Bool :=
  forceN MM fun m =>
  withU fun u1 u2 u4 u5 u6 =>
  tbPK m u1 fun t1 => tbPK m u2 fun t2 => tbPK m u4 fun t4 => tbPK m u5 fun t5 =>
  tbPK m u6 fun t6 =>
  linK (b0Coef t1 t2 t4 t5 t6 c) fun u0 => tbPK m u0 fun t0 =>
  herUUK m u0 u1 u2 u4 u5 u6 fun h => tblK m h fun th =>
  vtxMK m ⟨t0, t1, t2, t4, t5, t6, th⟩ u0 h c fun V =>
    V.testBit (rootL + 64) &&
      match runLv m ⟨t0, t1, t2, t4, t5, t6, th⟩ V c (2 ^ (rootL + 64)) lvls with
      | none => false
      | some S => Nat.land V (Nat.xor S m) >>> 64 == 0

@[expose] def rowCheck (row : Array Nat) (rootL : Nat) (lvls : List (List Nat)) : Bool :=
  forceV7 (rowN row) fun c =>
    (c.x0 < 49 && c.x1 < 49 && c.x2 < 49 && c.x3 < 49 && c.x4 < 49 && c.x5 < 49 && c.x6 < 49) &&
      c.x3 == 1 && isFFN c && decide (lvls.length ≤ 6) && decide (rootL < NL) &&
      rowCore c rootL lvls

end CFSG.Certificates.Kernel.Q7Bits
