module

public import Certificates.Data.D5Twist

public section

namespace Certificates.D5TwistK

open Certificates.D5Twist

@[expose] def dg (x k : Nat) : Nat := x / 4 ^ k % 4

@[expose] def pk (f : Nat → Nat) : Nat → Nat → Nat
  | _, 0 => 0
  | k, n + 1 => f k % 4 + 4 * pk f (k + 1) n

@[expose] def decN (n x : Nat) : Array Nat := Array.ofFn (n := n) fun k => dg x k.val

@[expose] def encA (a : Array Nat) : Nat := pk (fun k => a[k]!) 0 25

@[expose] def entK (x y k : Nat) : Nat :=
  (dg x (5 * (k / 5)) * dg y (k % 5) + dg x (5 * (k / 5) + 1) * dg y (5 + k % 5) +
    dg x (5 * (k / 5) + 2) * dg y (10 + k % 5) + dg x (5 * (k / 5) + 3) * dg y (15 + k % 5) +
    dg x (5 * (k / 5) + 4) * dg y (20 + k % 5)) % 3

@[expose] def mulK (x y : Nat) : Nat := pk (entK x y) 0 25

@[expose] def entV (a v i : Nat) : Nat :=
  (dg a (5 * i) * dg v 0 + dg a (5 * i + 1) * dg v 1 + dg a (5 * i + 2) * dg v 2 +
    dg a (5 * i + 3) * dg v 3 + dg a (5 * i + 4) * dg v 4) % 3

@[expose] def mvK (a v : Nat) : Nat := pk (entV a v) 0 5

@[expose] def idK : Nat := 281543712968705

@[expose] def minusOneK : Nat := 563087425937410

@[expose] def negK (a : Nat) : Nat := mulK minusOneK a

@[expose] def xvK : Nat := 665

@[expose] def simple5K : List Nat :=
  [281543712968710, 281543713055745, 281543733940225, 281891605319681, 633387433857025]

@[expose] def ccaK (gens : List Nat) : Nat → List Nat → List Nat → List Nat
  | 0, _, seen => seen
  | _ + 1, [], seen => seen
  | n + 1, r :: front, seen =>
    let new := (gens.map fun s => mulK (mulK s r) s).foldl
      (fun acc t => if seen.contains t || acc.contains t then acc else acc ++ [t]) []
    ccaK gens n (front ++ new) (seen ++ new)

@[expose] def ccK (seed gens : List Nat) : List Nat := ccaK gens 500 seed seed

@[expose] def S0K (_ : Unit := ()) : List Nat := ccK simple5K simple5K

@[expose] def allVK : List Nat := (List.range 243).map fun k => pk (fun i => k / 3 ^ i % 3) 0 5

@[expose] def fixedVK (S : List Nat) : List Nat := allVK.filter fun v => S.all fun s => mvK s v == v

@[expose] def nzK (z : Nat) : Nat :=
  if dg z 0 != 0 then dg z 0 else if dg z 1 != 0 then dg z 1 else if dg z 2 != 0 then dg z 2
  else if dg z 3 != 0 then dg z 3 else dg z 4

@[expose] def lineK (z : Nat) : Nat := pk (fun i => dg z i * nzK z % 3) 0 5

@[expose] def zlineK (z : Nat) : List Nat := [0, z, pk (fun i => 2 * dg z i % 3) 0 5]

@[expose] def wjGensK (b : Nat) : List Nat := ((List.range 4).filter (· != b)).map fun i => simple5K[i]!

@[expose] def prodWordK (gs : List Nat) (w : List Nat) : Nat := w.foldl (fun acc i => mulK acc gs[i]!) idK

@[expose] def invAuxK (g : Nat) : Nat → Nat → Nat → Nat
  | 0, _, prev => prev
  | n + 1, cur, prev => if cur == idK then prev else invAuxK g n (mulK g cur) cur

@[expose] def invK (g : Nat) : Nat := invAuxK g 1000 g idK

@[expose] def gsK (ra : Nat) : List Nat := simple5K ++ [ra]

@[expose] def spK (ra : Nat) : List Nat := ccK (gsK ra) (gsK ra)

@[expose] def wjK (b : Nat) : List Nat := ccK (wjGensK b) (wjGensK b)

@[expose] def linesK (b : Nat) : List Nat :=
  (fixedVK (wjK b)).filter fun z => z != 0 && lineK z == z

@[expose] def rzK (ra z : Nat) : List Nat := (spK ra).filter fun r => mvK r z == z

@[expose] def ozK (b ra z : Nat) : List Nat := ccK (wjK b) (rzK ra z)

@[expose] def lines15K (b ra : Nat) : List Nat := (linesK b).filter fun z => (ozK b ra z).length == 15

@[expose] def forcedK (b ra : Nat) : List Nat := (lines15K b ra).flatMap (ozK b ra)

@[expose] def clK (b ra : Nat) : List Nat := ccK (S0K () ++ forcedK b ra) (S0K () ++ forcedK b ra)

@[expose] def restK (gs sp wj lines lines15 : List Nat) (oz : Nat → List Nat) (forced cl : List Nat) :
    Bool :=
  (gs.all fun s => mulK s s == idK) &&
  (sp.all fun r => mulK r r == idK) &&
  (sp.all fun r => gs.all fun s => sp.contains (mulK (mulK s r) s)) &&
  (wj.length == 6) && (lines.length == 4) && (lines15.length == 2) &&
  (lines15.all fun z => lineK z != xvK) &&
  (lines15.all fun z => (fixedVK (oz z)).all fun v => (zlineK z).contains v) &&
  (forced.all fun r => mulK r r == idK) &&
  (sp.all fun r => cl.contains r)

@[expose] def BK (b ra : Nat) : Bool :=
  restK (gsK ra) (spK ra) (wjK b) (linesK b) (lines15K b ra) (ozK b ra) (forcedK b ra) (clK b ra)

@[expose] def pairsK : List (Nat × Nat) :=
  [(0, 282645372080130), (0, 565217983992833), (0, 299170275528705), (0, 598203062309153),
   (2, 299170275528705), (2, 598203062309153), (2, 282645372080130), (2, 565217983992833),
   (3, 299170275528705), (3, 598203062309153), (3, 282645372080130), (3, 565217983992833)]

@[expose] def ch712503B (i : Nat) : Bool := BK (pairsK.getD i (0, 0)).1 (pairsK.getD i (0, 0)).2

@[expose] def raK (g gi : Nat) : Nat := mulK (mulK g simple5K[4]!) gi

@[expose] def caseAK3 (gA : Array Nat) (g gi b : Nat) (neg : Bool) (w : List Nat) : Bool :=
  (decN 25 g == gA) && (mulK g gi == idK) && (w.all fun i => i < 6) &&
  (prodWordK (gsK (raK g gi)) w == (if neg then negK g else g)) && pairsK.contains (b, raK g gi)

@[expose] def caseAK2 (gA : Array Nat) (g b : Nat) (neg : Bool) (w : List Nat) : Bool :=
  caseAK3 gA g (invK g) b neg w

@[expose] def caseAK (b : Nat) (gA : Array Nat) (neg : Bool) (w : List Nat) : Bool :=
  caseAK2 gA (encA gA) b neg w

@[expose] def ch712503A (_ : Unit := ()) : Bool :=
  wordTable.all fun e =>
    caseAK e.1 (cG #[e.2.1, 1, e.2.2.1, e.2.2.2.1] e.2.2.2.2.1 e.2.2.2.2.2.1) e.2.2.2.2.2.2.1
      e.2.2.2.2.2.2.2

@[expose] def ch712503S (_ : Unit := ()) : Bool :=
  ((S0K ()).length == 20) && ((S0K ()).all fun r => mulK r r == idK) && (wordTable.length == 40)

@[expose] def ch712503L (_ : Unit := ()) : Bool :=
  (simple5 () == simple5K.map (decN 25)) && (sRefl 4 == decN 25 simple5K[4]!) &&
  (simple5K.all fun s => s < 4 ^ 25) &&
  (idM == decN 25 idK) && (idK < 4 ^ 25) && (minusOneM == decN 25 minusOneK) &&
  (xv == decN 5 xvK) && (xvK < 4 ^ 5) && (#[0, 0, 0, 0, 0] == decN 5 0) &&
  (allVecs () == allVK.map (decN 5)) &&
  (allVK.all fun z => lineOf (decN 5 z) == decN 5 (lineK z) &&
    zline (decN 5 z) == (zlineK z).map (decN 5) && (zlineK z).all fun v => v < 4 ^ 5) &&
  ([0, 2, 3].all fun b => wjGens b == (wjGensK b).map (decN 25) &&
    (wjGensK b).all fun s => s < 4 ^ 25)

end Certificates.D5TwistK

end
