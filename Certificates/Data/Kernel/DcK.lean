module

public import Certificates.Data.CFSGNative.H13.LocDblDc
public import Certificates.Data.Kernel.E64F
public import Certificates.Data.Kernel.LocalQT.PermW

public section

namespace CFSG.KC.DcK

open CFSG.Quasithin.H13.LocDbl.DcNative CFSG.KC.E64F

@[expose] def splitGo (c : Char) : List Char → List Char → List (List Char)
  | [], acc => [acc.reverse]
  | x :: xs, acc => if x == c then acc.reverse :: splitGo c xs [] else splitGo c xs (x :: acc)

@[expose] def digitsK (l : List Char) : List Nat := l.map fun c => c.toNat - '0'.toNat

@[expose] def decK (l : List Char) : Nat := l.foldl (fun n c => n * 10 + (c.toNat - 48)) 0

@[expose] def isNum (l : List Char) : Bool := !l.isEmpty && l.all Char.isDigit

@[expose] def wordsK (cs : List Char) : List (List Nat) :=
  ((splitGo ',' cs []).filter fun l => !l.isEmpty).map digitsK

@[expose] def numsK : List (List Char) → Option (List Nat)
  | [] => some []
  | p :: ps => if isNum p then (numsK ps).map (decK p :: ·) else none

@[expose] def natsK (cs : List Char) : Option (List Nat) := numsK (splitGo ' ' cs [])

@[expose] def edgeK (e : List Char) : Option (Nat × Nat × List Nat) :=
  match splitGo ' ' e [] with
  | [a, b, w] => if isNum a && isNum b then some (decK a, decK b, digitsK w) else none
  | _ => none

@[expose] def edgesGo : List (List Char) → Option (List (Nat × Nat × List Nat))
  | [] => some []
  | p :: ps => match edgeK p with
    | some e => (edgesGo ps).map (e :: ·)
    | none => none

@[expose] def edgesK (cs : List Char) : Option (List (Nat × Nat × List Nat)) :=
  edgesGo ((splitGo ',' cs []).filter fun l => !l.isEmpty)

structure EnumK where
  N : Nat
  par : Nat → Nat
  lab : Nat → Nat
  cnt : Nat → Nat
  sig : Nat → Nat
  sinv : Nat → Nat
  pos : Nat → Nat
  row : Nat → List Nat
  tgt : Nat → Nat → Nat

@[expose] def EnumK.key (n r : Nat) (E : EnumK) (k : Nat) : Nat := keyNat n r (E.row k)

@[expose] def EnumK.skey (n r : Nat) (E : EnumK) (p : Nat) : Nat := E.key n r (E.sig p)

@[expose] def replayStep (E : EnumK) (i t c : Nat) : Option Nat :=
  if E.tgt i t == c then
    (if decide (c < E.N) && E.par c == i && E.lab c == t then some (c + 1) else none)
  else if decide (E.tgt i t < c) then some c else none

@[expose] def replayRow (E : EnumK) (i : Nat) : List Nat → Nat → Option Nat
  | [], c => some c
  | t :: ts, c => match replayStep E i t c with
    | some c' => replayRow E i ts c'
    | none => none

@[expose] def elemK (n : Nat) (B : List Nat) (G : Nat → Nat → Nat) (m : Nat) (E : EnumK)
    (k : Nat) : Bool :=
  (if k == 0 then E.row 0 == B && E.par 0 == 0 && E.lab 0 == 0 && E.cnt 0 == 1
    else decide (E.par k < k) && decide (E.lab k < m) &&
      E.row k == (E.row (E.par k)).map (G (E.lab k))) &&
  (List.range m).all (fun t => decide (E.tgt k t < E.N) &&
    (E.row k).map (G t) == E.row (E.tgt k t)) &&
  decide (E.sig k < E.N) && E.sinv (E.sig k) == k && decide (E.sinv k < E.N) &&
    E.sig (E.sinv k) == k &&
  (decide (E.N ≤ k + 1) || decide (E.skey n B.length k < E.skey n B.length (k + 1))) &&
  decide (k < E.cnt k) &&
  replayRow E k (List.range m) (E.cnt k) == some (if k + 1 < E.N then E.cnt (k + 1) else E.N)

@[expose] def elemsK (n : Nat) (B : List Nat) (G : Nat → Nat → Nat) (m : Nat) (E : EnumK)
    (lo len : Nat) : Bool :=
  (List.range' lo len).all (elemK n B G m E)

@[expose] def enumHd (n : Nat) (B : List Nat) (cap : Nat) (E : EnumK) : Bool :=
  decide (0 < E.N) && decide (E.N ≤ cap) && B.all fun b => decide (b < n)

@[expose] noncomputable def recK (N r : Nat) (T : Nat → Nat) : EnumK where
  N := N
  par k := CFSG.KC.LQT.PW.imgW 14 (T k) r
  lab k := CFSG.KC.LQT.PW.imgW 14 (T k) (r + 1)
  cnt k := CFSG.KC.LQT.PW.imgW 14 (T k) (r + 2)
  sig k := CFSG.KC.LQT.PW.imgW 14 (T k) (r + 3)
  sinv k := CFSG.KC.LQT.PW.imgW 14 (T k) (r + 4)
  pos k := CFSG.KC.LQT.PW.imgW 14 (T k) (r + 5)
  row k := (List.range r).map (CFSG.KC.LQT.PW.imgW 14 (T k))
  tgt k t := CFSG.KC.LQT.PW.imgW 14 (T k) (r + 6 + t)

@[expose] def orbGens (L : Nat → Nat → Nat) (vt lb : Nat → Nat) (c x : Nat) :
    List Nat → Nat → Option Nat
  | [], cnt => some cnt
  | t :: ts, cnt =>
    if decide (vt (L t x) < cnt) then orbGens L vt lb c x ts cnt
    else if vt (L t x) == cnt && lb (L t x) == c then orbGens L vt lb c x ts (cnt + 1)
    else none

@[expose] def orbQueue (L : Nat → Nat → Nat) (m : Nat) (Q vt lb : Nat → Nat) (c : Nat) :
    Nat → Nat → Nat → Option Nat
  | 0, _, cnt => some cnt
  | f + 1, h, cnt =>
    if decide (h < cnt) then
      match orbGens L vt lb c (Q h) (List.range m) cnt with
      | some cnt' => orbQueue L m Q vt lb c f (h + 1) cnt'
      | none => none
    else some cnt

@[expose] def orbScan (n : Nat) (L : Nat → Nat → Nat) (m : Nat) (Q vt lb : Nat → Nat) :
    List Nat → Nat → Nat → Option Nat
  | [], _, cnt => some cnt
  | s :: ss, c, cnt =>
    if decide (vt s < cnt) then orbScan n L m Q vt lb ss c cnt
    else if vt s == cnt && lb s == c then
      match orbQueue L m Q vt lb c n cnt (cnt + 1) with
      | some cnt' => orbScan n L m Q vt lb ss (c + 1) cnt'
      | none => none
    else none

@[expose] def orbCK (n : Nat) (L : Nat → Nat → Nat) (m : Nat) (Q vt lb : Nat → Nat) : Bool :=
  (List.range n).all (fun y => decide (vt y < n) && Q (vt y) == y && decide (Q y < n) &&
      vt (Q y) == y && decide (lb y < n)) &&
    orbScan n L m Q vt lb (List.range n) 0 0 == some n

@[expose] def memK (n r : Nat) (E : EnumK) (x p : Nat) : Option Bool :=
  if decide (p < E.N) && E.skey n r p == x then some true
  else if (p == 0 || decide (E.skey n r (p - 1) < x)) &&
      (decide (E.N ≤ p) || decide (x < E.skey n r p)) && decide (p ≤ E.N) then some false
  else none

@[expose] def cntK (f : Nat → Option Bool) : List Nat → Nat → Option Nat
  | [], a => some a
  | k :: ks, a => match f k with
    | some true => cntK f ks (a + 1)
    | some false => cntK f ks a
    | none => none

@[expose] def cntB (f : Nat → Bool) : List Nat → Nat → Nat
  | [], a => a
  | k :: ks, a => if f k then cntB f ks (a + 1) else cntB f ks a

@[expose] def sumK (f : Nat → Nat) : List Nat → Nat → Nat
  | [], a => a
  | k :: ks, a => sumK f ks (a + f k)

@[expose] def allNe : List Nat → Bool
  | [] => true
  | x :: xs => xs.all (fun y => y != x) && allNe xs

@[expose] def optL (f : Nat → Option Nat) : List Nat → Option (List Nat)
  | [] => some []
  | k :: ks => match f k with
    | some v => (optL f ks).map (v :: ·)
    | none => none

structure DcK where
  n : Nat
  B : List Nat
  ab : Nat → Nat → Nat
  nr : Nat
  rt : Nat → Nat → Nat
  rti : Nat → Nat → Nat
  R : EnumK
  lb : Nat → Nat
  reps : Array (List Nat)
  edges : Array (Nat × Nat × List Nat)
  c0 : Nat
  inEdge : Array Nat
  dIn : Array Nat
  reach : List Nat
  outEdge : Array Nat
  dOut : Array Nat
  Vs : List (List (List Nat) × (Nat → Nat → Nat) × EnumK)
  order : Nat
  hpos : Nat → Nat → Nat

namespace DcK

variable (K : DcK)

@[expose] def vg (ex : Nat → Nat → Nat) (t : Nat) : Nat → Nat :=
  if t < K.nr then K.rt t else ex (t - K.nr)

@[expose] def edgeL (w : List Nat) (l p : Nat) : Nat :=
  if l < K.nr then K.rt l p
  else if l < K.nr + K.nr then K.rti (l - K.nr) p
  else if l = K.nr + K.nr then wordF K.ab w p
  else wordF K.ab (invW w) p

@[expose] def evalE (w e : List Nat) (p : Nat) : Nat := e.foldr (fun l q => K.edgeL w l q) p

@[expose] def ePts (E : EnumK) (G : Nat → Nat → Nat) : Nat → Nat → List Nat → List Nat
  | 0, _, ps => ps
  | f + 1, k, ps => if k == 0 then ps else (ePts E G f (E.par k) ps).map (G (E.lab k))

@[expose] def conjKey (j k : Nat) : Nat :=
  keyNat K.n K.B.length ((ePts K.R K.rt (k + 1) k
    (K.B.map (wordF K.ab (K.reps.getD j [])))).map (wordF K.ab (invW (K.reps.getD j []))))

@[expose] def invOK : Bool :=
  (List.range K.n).all fun q => K.ab 2 (K.ab 0 q) == q && K.ab 3 (K.ab 1 q) == q &&
    (List.range K.nr).all fun t => K.rti t (K.rt t q) == q

@[expose] def basicOK : Bool :=
  K.B.all (fun b => decide (b < K.n)) && decide (0 < K.R.N) &&
    K.reps.toList.all (fun w => w.all fun l => decide (l < 4)) &&
    decide (K.c0 < K.reps.size) && K.reach.all (fun j => decide (j < K.reps.size)) &&
    decide (K.Vs.length ≤ 3) && K.Vs.all (fun V => V.1.all fun w => w.all fun l => decide (l < 4))

@[expose] def labOK : Bool :=
  (List.range K.nr).all fun t => (List.range K.n).all fun q => K.lb (K.rt t q) == K.lb q

@[expose] def inv (j : Nat) : Nat :=
  sumK (fun q => wt (K.lb q) (K.lb (wordF K.ab (K.reps.getD j []) q))) (List.range K.n) 0

@[expose] def distOK (I : List Nat) : Bool :=
  I.length == K.reps.size && (List.range K.reps.size).all (fun j => K.inv j == I.getD j 0) &&
    allNe I

@[expose] def edgesOK : Bool :=
  K.edges.toList.all (fun ed => decide (ed.1 < K.reps.size) && decide (ed.2.1 < K.reps.size) &&
      ed.2.2.all (fun l => decide (l < K.nr + K.nr + 2)) &&
      K.B.all fun b => wordF K.ab (K.reps.getD ed.2.1 []) b ==
        K.evalE (K.reps.getD ed.1 []) ed.2.2 b) &&
    inTreeOK K.reps.size K.c0 K.edges K.inEdge K.dIn &&
    outTreeOK K.c0 K.reach K.edges K.outEdge K.dOut && allNe K.reach

@[expose] def vsOK : Bool := K.Vs.all fun V => decide (0 < V.2.2.N) && decide (V.2.2.N < K.order)

@[expose] def hit (j : Nat) : Option Nat :=
  cntK (fun k => memK K.n K.B.length K.R (K.conjKey j k) (K.hpos j k)) (List.range K.R.N) 0

@[expose] def hitOK (H : List Nat) : Bool :=
  H.length == K.reps.size && (List.range K.reps.size).all fun j => K.hit j == some (H.getD j 0)

@[expose] def ulb : Nat :=
  match K.Vs with
  | [] => 0
  | [V0] => V0.2.2.N
  | V0 :: V1 :: _ => V0.2.2.N + cntB (fun k => memK K.n K.B.length V0.2.2
      (V1.2.2.key K.n K.B.length k) (V1.2.2.pos k) == some false) (List.range V1.2.2.N) 0

@[expose] def massOK (H : List Nat) : Bool :=
  decide (K.order < 2 * (K.reach.map fun j => K.R.N * (K.R.N / H.getD j 0)).sum) &&
    decide (K.order ≤ (H.map fun h => K.R.N * (K.R.N / h)).sum + K.ulb)

end DcK

@[expose] def chkAllK (K : DcK) (I H : List Nat) : Bool :=
  K.invOK && K.basicOK && K.labOK && K.distOK I && K.edgesOK && K.vsOK && K.hitOK H && K.massOK H

end CFSG.KC.DcK

end
