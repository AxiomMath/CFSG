module

public import Certificates.Data.Kernel.D5TwistK

public section

namespace Certificates.D5TwistK

open Certificates.D5Twist

@[expose] def LF : Nat := 375299968947541

@[expose] def CMF : Nat := 3301759257603

@[expose] noncomputable def nrmF (x : Nat) : Nat :=
  (fun b => Nat.xor x (Nat.lor b (Nat.shiftLeft b 1))) (Nat.land (Nat.land x (Nat.shiftRight x 1)) LF)

@[expose] noncomputable def colF (x j : Nat) : Nat :=
  (fun c => (fun t => (fun t => Nat.lor t (Nat.shiftLeft c 8)) (Nat.lor t (Nat.shiftLeft t 4)))
    (Nat.lor c (Nat.shiftLeft c 2))) (Nat.land (Nat.shiftRight x (2 * j)) CMF)

@[expose] noncomputable def rowF (y j : Nat) : Nat :=
  (fun r => (fun u => (fun u => Nat.lor u (Nat.shiftLeft r 40)) (Nat.lor u (Nat.shiftLeft u 20)))
    (Nat.lor r (Nat.shiftLeft r 10))) (Nat.land (Nat.shiftRight y (10 * j)) 1023)

@[expose] noncomputable def termF (X Y : Nat) : Nat × Nat :=
  (fun a1 a2 b1 b2 =>
      (Nat.lor (Nat.land a1 b1) (Nat.land a2 b2), Nat.lor (Nat.land a1 b2) (Nat.land a2 b1)))
    (Nat.land X LF) (Nat.land (Nat.shiftRight X 1) LF) (Nat.land Y LF)
    (Nat.land (Nat.shiftRight Y 1) LF)

@[expose] noncomputable def addF (a b : Nat × Nat) : Nat × Nat :=
  (fun t => (Nat.xor (Nat.lor a.2 b.2) t, Nat.xor (Nat.lor a.1 b.1) t))
    (Nat.xor (Nat.lor a.1 b.2) (Nat.lor a.2 b.1))

@[expose] noncomputable def tjF (x y j : Nat) : Nat × Nat := termF (colF x j) (rowF y j)

@[expose] noncomputable def mulNF (x y : Nat) : Nat :=
  (fun z : Nat × Nat => Nat.lor z.1 (Nat.shiftLeft z.2 1))
    (addF (addF (addF (addF (tjF x y 0) (tjF x y 1)) (tjF x y 2)) (tjF x y 3)) (tjF x y 4))

@[expose] noncomputable def mulF (x y : Nat) : Nat := mulNF (nrmF x) (nrmF y)

@[expose] noncomputable def negF (a : Nat) : Nat := mulF minusOneK a

@[expose] noncomputable def ccaF (gens : List Nat) : Nat → List Nat → List Nat → List Nat
  | 0, _, seen => seen
  | _ + 1, [], seen => seen
  | n + 1, r :: front, seen =>
    let new := (gens.map fun s => mulF (mulF s r) s).foldl
      (fun acc t => if seen.contains t || acc.contains t then acc else acc ++ [t]) []
    ccaF gens n (front ++ new) (seen ++ new)

@[expose] noncomputable def ccF (seed gens : List Nat) : List Nat := ccaF gens 500 seed seed

@[expose] noncomputable def S0F (_ : Unit := ()) : List Nat := ccF simple5K simple5K

@[expose] noncomputable def prodWordF (gs : List Nat) (w : List Nat) : Nat :=
  w.foldl (fun acc i => mulF acc gs[i]!) idK

@[expose] noncomputable def invAuxF (g : Nat) : Nat → Nat → Nat → Nat
  | 0, _, prev => prev
  | n + 1, cur, prev => if cur == idK then prev else invAuxF g n (mulF g cur) cur

@[expose] noncomputable def invF (g : Nat) : Nat := invAuxF g 1000 g idK

@[expose] noncomputable def spF (ra : Nat) : List Nat := ccF (gsK ra) (gsK ra)

@[expose] noncomputable def wjF (b : Nat) : List Nat := ccF (wjGensK b) (wjGensK b)

@[expose] noncomputable def linesF (b : Nat) : List Nat :=
  (fixedVK (wjF b)).filter fun z => z != 0 && lineK z == z

@[expose] noncomputable def rzF (ra z : Nat) : List Nat := (spF ra).filter fun r => mvK r z == z

@[expose] noncomputable def ozF (b ra z : Nat) : List Nat := ccF (wjF b) (rzF ra z)

@[expose] noncomputable def lines15F (b ra : Nat) : List Nat :=
  (linesF b).filter fun z => (ozF b ra z).length == 15

@[expose] noncomputable def forcedF (b ra : Nat) : List Nat := (lines15F b ra).flatMap (ozF b ra)

@[expose] noncomputable def clF (b ra : Nat) : List Nat :=
  ccF (S0F () ++ forcedF b ra) (S0F () ++ forcedF b ra)

@[expose] noncomputable def restF (gs sp wj lines lines15 : List Nat) (oz : Nat → List Nat)
    (forced cl : List Nat) : Bool :=
  (gs.all fun s => mulF s s == idK) &&
  (sp.all fun r => mulF r r == idK) &&
  (sp.all fun r => gs.all fun s => sp.contains (mulF (mulF s r) s)) &&
  (wj.length == 6) && (lines.length == 4) && (lines15.length == 2) &&
  (lines15.all fun z => lineK z != xvK) &&
  (lines15.all fun z => (fixedVK (oz z)).all fun v => (zlineK z).contains v) &&
  (forced.all fun r => mulF r r == idK) &&
  (sp.all fun r => cl.contains r)

@[expose] noncomputable def BF (b ra : Nat) : Bool :=
  restF (gsK ra) (spF ra) (wjF b) (linesF b) (lines15F b ra) (ozF b ra) (forcedF b ra) (clF b ra)

@[expose] noncomputable def ch712503BF (i : Nat) : Bool :=
  BF (pairsK.getD i (0, 0)).1 (pairsK.getD i (0, 0)).2

@[expose] noncomputable def raF (g gi : Nat) : Nat := mulF (mulF g simple5K[4]!) gi

@[expose] noncomputable def caseAF3 (gA : Array Nat) (g gi b : Nat) (neg : Bool) (w : List Nat) :
    Bool :=
  (decN 25 g == gA) && (mulF g gi == idK) && (w.all fun i => i < 6) &&
  (prodWordF (gsK (raF g gi)) w == (if neg then negF g else g)) && pairsK.contains (b, raF g gi)

@[expose] noncomputable def caseAF2 (gA : Array Nat) (g b : Nat) (neg : Bool) (w : List Nat) :
    Bool :=
  caseAF3 gA g (invF g) b neg w

@[expose] noncomputable def caseAF (b : Nat) (gA : Array Nat) (neg : Bool) (w : List Nat) : Bool :=
  caseAF2 gA (encA gA) b neg w

@[expose] noncomputable def ch712503AF (_ : Unit := ()) : Bool :=
  wordTable.all fun e =>
    caseAF e.1 (cG #[e.2.1, 1, e.2.2.1, e.2.2.2.1] e.2.2.2.2.1 e.2.2.2.2.2.1) e.2.2.2.2.2.2.1
      e.2.2.2.2.2.2.2

@[expose] noncomputable def ch712503SF (_ : Unit := ()) : Bool :=
  ((S0F ()).length == 20) && ((S0F ()).all fun r => mulF r r == idK) && (wordTable.length == 40)

end Certificates.D5TwistK

end
