module

public import CFSG.Certificates.Kernel.Enum.Defs
public import Certificates.Data.Kernel.Spor.Chain
public import Mathlib.Data.List.Sort
public import Mathlib.Data.Nat.Digits.Defs

public section

namespace CFSG.KC.Census

open CFSG.KC.Enum

@[expose] noncomputable def at' (w p i : Nat) : Nat := pg w (CFSG.KS.mask w) p i

@[expose] noncomputable def pc (n w p q : Nat) : Nat := pcomp n w (CFSG.KS.mask w) p q

@[expose] noncomputable def pid (n w : Nat) : Nat := pidn n w

@[expose] noncomputable def pset (w p j v : Nat) : Nat :=
  Nat.add (Nat.sub p (Nat.shiftLeft (at' w p j) (Nat.mul w j))) (Nat.shiftLeft v (Nat.mul w j))

@[expose] noncomputable def pinv (n w p : Nat) : Nat :=
  (List.range n).foldl (fun r i =>
    strictN r fun r => nIf(Nat.blt (at' w p i) n, pset w r (at' w p i) i, r)) 0

@[expose] noncomputable def pvalid (n w p : Nat) : Bool :=
  strictB (pinv n w p) fun r =>
    (List.range n).all fun i => Nat.blt (at' w p i) n && Nat.beq (at' w r (at' w p i)) i

@[expose] noncomputable def pkey (n w : Nat) (ps : List Nat) (p : Nat) : Nat :=
  Nat.ofDigits n (ps.map fun q => at' w p q)

@[expose] noncomputable def pprod (n w : Nat) (l : List Nat) : Nat := l.foldr (pc n w) (pid n w)

@[expose] noncomputable def ppow (n w p m : Nat) : Nat := pprod n w (List.replicate m p)

@[expose] noncomputable def pmask (n w : Nat) (basis : Array Nat) (m : Nat) : Nat :=
  pprod n w (((List.range basis.size).filter fun k => m.testBit k).map fun k => basis[k]!)

@[expose] noncomputable def pcommA (n w p q : Nat) : Bool := Nat.beq (pc n w p q) (pc n w q p)

@[expose] noncomputable def pcomm (n w g h : Nat) : Nat :=
  pc n w (pc n w g h) (pc n w (pinv n w g) (pinv n w h))

@[expose] noncomputable def pconj (n w g y : Nat) : Nat := pc n w g (pc n w y (pinv n w g))

structure GFacP where
  t : Nat
  c₁ : Nat
  c₂ : Nat
deriving Inhabited

structure NFacP where
  e : Nat
  γ : List GFacP
deriving Inhabited

structure CFacP where
  x₁ : Nat
  x₂ : Nat
deriving Inhabited

inductive WitP where
  | order4 (w : List NFacP) (m : Nat)
  | twoGroup (gens : List (List NFacP × Nat)) (k : Nat)
  | perfect (gens : List (List GFacP × Nat)) (comms : List (Nat × Nat)) (x k : Nat)
      (conjs : List Nat) (e g : Nat)
  | inX
  | small
  | closing (s t c kc v : Nat) (gens : List (List CFacP × Nat)) (comms : List (Nat × Nat))
deriving Inhabited

@[expose] def WitP.isMono : WitP → Bool
  | .order4 .. => true
  | .perfect .. => true
  | _ => false

structure NodeP where
  basis : Array Nat
  wit : WitP
  children : Array Nat
deriving Inhabited

structure ArrCertP where
  pts : Array Nat
  edges : Array (Array Nat)
  par : Array Nat
  lab : Array Nat
deriving Inhabited

section Checks

variable (n w : Nat)

@[expose] noncomputable def GFacP.val (f : GFacP) : Nat := pcomm n w f.c₁ f.c₂

@[expose] noncomputable def GFacP.ok (inX : Nat → Bool) (basis : Array Nat) (f : GFacP) : Bool :=
  !(Nat.beq (pmask n w basis f.t) (pid n w)) && pvalid n w f.c₁ && pvalid n w f.c₂ && inX f.c₁ &&
    inX f.c₂ && pcommA n w f.c₁ (pmask n w basis f.t) && pcommA n w f.c₂ (pmask n w basis f.t)

@[expose] noncomputable def pgamma (l : List GFacP) : Nat := pprod n w (l.map (GFacP.val n w))

@[expose] noncomputable def NFacP.val (basis : Array Nat) (f : NFacP) : Nat :=
  pcomm n w (pmask n w basis f.e) (pgamma n w f.γ)

@[expose] noncomputable def NFacP.ok (inX : Nat → Bool) (basis : Array Nat) (f : NFacP) : Bool :=
  f.γ.all (GFacP.ok n w inX basis) && pvalid n w (pmask n w basis f.e) &&
    pvalid n w (pgamma n w f.γ)

@[expose] noncomputable def pnA (basis : Array Nat) (l : List NFacP) : Nat :=
  pprod n w (l.map (NFacP.val n w basis))

@[expose] noncomputable def CFacP.val (f : CFacP) : Nat := pcomm n w f.x₁ f.x₂

@[expose] noncomputable def CFacP.ok (inX : Nat → Bool) (basis : Array Nat) (f : CFacP) : Bool :=
  pvalid n w f.x₁ && pvalid n w f.x₂ && inX f.x₁ && inX f.x₂ &&
    (List.range basis.size).all fun k => pcommA n w f.x₁ basis[k]! && pcommA n w f.x₂ basis[k]!

@[expose] def pmem (c : ArrCertP) (a : Nat) : Bool := c.pts.toList.any (Nat.beq a)

@[expose] def pcount (outX : Nat → Bool) (c : ArrCertP) : Nat :=
  (c.pts.toList.filter fun a => outX a).length

@[expose] def asc : List Nat → Bool
  | a :: b :: l => Nat.blt a b && asc (b :: l)
  | _ => true

@[expose] noncomputable def ppointOK (gs : Array Nat) (c : ArrCertP) (i : Nat) : Bool :=
  pvalid n w c.pts[i]! && Nat.beq (c.edges[i]!).size gs.size &&
    (List.range gs.size).all (fun k => Nat.blt (c.edges[i]![k]!) c.pts.size &&
      Nat.beq c.pts[c.edges[i]![k]!]! (pc n w gs[k]! c.pts[i]!)) &&
    (Nat.beq i 0 || (Nat.blt c.par[i]! i && Nat.blt c.lab[i]! gs.size &&
      Nat.beq c.pts[i]! (pc n w gs[c.lab[i]!]! c.pts[c.par[i]!]!)))

@[expose] noncomputable def ppointAt (gs : Array Nat) (c : ArrCertP) (i u : Nat) (e : Array Nat)
    (pa la : Nat) : Bool :=
  pvalid n w u && Nat.beq e.size gs.size &&
    (List.range gs.size).all (fun k => Nat.blt e[k]! c.pts.size &&
      Nat.beq c.pts[e[k]!]! (pc n w gs[k]! u)) &&
    (Nat.beq i 0 || (Nat.blt pa i && Nat.blt la gs.size &&
      Nat.beq u (pc n w gs[la]! c.pts[pa]!)))

@[expose] noncomputable def ppointsOK (gs : Array Nat) (c : ArrCertP) :
    Nat → List Nat → List (Array Nat) → List Nat → List Nat → Bool
  | _, [], _, _, _ => true
  | i, u :: us, es, ps, ls =>
    ppointAt n w gs c i u (es.headD #[]) (ps.headD 0) (ls.headD 0) &&
      ppointsOK gs c (i + 1) us es.tail ps.tail ls.tail

@[expose] noncomputable def penumOK (gs : Array Nat) (ps : List Nat) (c : ArrCertP) : Bool :=
  ((List.range gs.size).all fun k => pvalid n w gs[k]!) &&
    (Nat.blt 0 c.pts.size && Nat.beq c.pts[0]! (pid n w) &&
      ppointsOK n w gs c 0 c.pts.toList c.edges.toList c.par.toList c.lab.toList &&
      asc ((c.pts.toList.map (pkey n w ps)).insertionSort (· ≤ ·)))

@[expose] noncomputable def pmaskCert (basis : Array Nat) : ArrCertP :=
  let r := List.range (2 ^ basis.size)
  ⟨(r.map (pmask n w basis)).toArray,
    (r.map fun i => ((List.range basis.size).map fun k => i ^^^ 2 ^ k).toArray).toArray,
    (r.map fun i => i - 2 ^ Nat.log2 i).toArray,
    (r.map Nat.log2).toArray⟩

@[expose] noncomputable def pwitOK (ps : List Nat) (inX outX : Nat → Bool)
    (allowPW allowInX allowU : Bool) (basis : Array Nat) (cE : ArrCertP) (cs : Array ArrCertP) :
    WitP → Bool
  | .order4 l m =>
    let y := ppow n w (pnA n w basis l) m
    l.all (NFacP.ok n w inX basis) && !(Nat.beq (pc n w y y) (pid n w)) &&
      Nat.beq (ppow n w y 4) (pid n w)
  | .twoGroup gens k =>
    let gs := (gens.map fun l => ppow n w (pnA n w basis l.1) l.2).toArray
    let cP := cs[0]!
    gens.all (fun l => l.1.all (NFacP.ok n w inX basis)) && penumOK n w gs ps cP &&
      Nat.beq cP.pts.size (2 ^ k) && Nat.blt (pcount outX cE) (2 ^ k)
  | .perfect gens comms x k conjs e g =>
    let gs := (gens.map fun l => ppow n w (pgamma n w l.1) l.2).toArray
    let cP := cs[0]!
    let m := cP.pts.size
    let qs := (comms.map fun ij => pcomm n w cP.pts[ij.1]! cP.pts[ij.2]!).toArray
    let cQ := cs[1]!
    let xa := cP.pts[x]!
    let rs := (conjs.map fun p => pconj n w cP.pts[p]! (pc n w xa xa)).toArray
    let cR := cs[2]!
    allowPW && gens.all (fun l => l.1.all (GFacP.ok n w inX basis)) && penumOK n w gs ps cP &&
      comms.all (fun ij => Nat.blt ij.1 m && Nat.blt ij.2 m) && penumOK n w qs ps cQ &&
      Nat.beq cQ.pts.size m && Nat.blt x m && Nat.beq (ppow n w xa (2 ^ k)) (pid n w) &&
      conjs.all (fun p => Nat.blt p m) && penumOK n w rs ps cR && Nat.beq cR.pts.size m &&
      Nat.blt g m && !(pcommA n w (pmask n w basis e) cP.pts[g]!)
  | .inX => allowInX && (List.range basis.size).all fun k => inX basis[k]!
  | .small => Nat.blt cE.pts.size 4
  | .closing s t c kc v gens comms =>
    let gs := (gens.map fun l => ppow n w (pprod n w (l.1.map (CFacP.val n w))) l.2).toArray
    let cP := cs[0]!
    let m := cP.pts.size
    let qs := (comms.map fun ij => pcomm n w cP.pts[ij.1]! cP.pts[ij.2]!).toArray
    let cQ := cs[1]!
    allowU && !(Nat.beq (pmask n w basis s) (pid n w)) &&
      !(Nat.beq (pmask n w basis t) (pid n w)) &&
      pvalid n w c && inX c && pcommA n w c (pmask n w basis t) &&
      Nat.beq (ppow n w c (2 ^ kc)) (pid n w) && pvalid n w (pmask n w basis v) &&
      Nat.beq (pcomm n w (pmask n w basis v) c) (pmask n w basis s) &&
      gens.all (fun l => l.1.all (CFacP.ok n w inX basis)) && penumOK n w gs ps cP &&
      comms.all (fun ij => Nat.blt ij.1 m && Nat.blt ij.2 m) && penumOK n w qs ps cQ &&
      Nat.beq cQ.pts.size m && pmem cP (pmask n w basis s)

@[expose] noncomputable def pchildOK (nodes : Array NodeP) (cN : Array ArrCertP) (i : Nat) (u : Nat)
    (j : Nat) : Bool :=
  Nat.blt j nodes.size &&
    ((List.range nodes[j]!.basis.size).all fun k =>
      pmem cN[i]! nodes[j]!.basis[k]! || pmem cN[i]! (pc n w u nodes[j]!.basis[k]!)) &&
    ((List.range nodes[i]!.basis.size).all fun k => pmem cN[j]! nodes[i]!.basis[k]!) &&
    pmem cN[j]! u

@[expose] def walkAll (f : Nat → Nat → Bool) : List Nat → List Nat → Bool
  | [], _ => true
  | u :: us, c :: cs => f u c && walkAll f us cs
  | u :: us, [] => f u 0 && walkAll f us []

@[expose] noncomputable def pnodeOK (ps : List Nat) (inX outX : Nat → Bool)
    (allowPW allowInX allowU : Bool) (cS : ArrCertP) (nodes : Array NodeP)
    (cN : Array ArrCertP) (wcs : Array (Array ArrCertP)) (i : Nat) : Bool :=
  penumOK n w nodes[i]!.basis ps cN[i]! &&
    pwitOK n w ps inX outX allowPW allowInX allowU nodes[i]!.basis cN[i]! wcs[i]! nodes[i]!.wit &&
    (nodes[i]!.wit.isMono || walkAll (fun u c =>
      !(Nat.beq (pc n w u u) (pid n w)) ||
        !((List.range nodes[i]!.basis.size).all fun k => pcommA n w u nodes[i]!.basis[k]!) ||
        pmem cN[i]! u || pchildOK n w nodes cN i u c) cS.pts.toList nodes[i]!.children.toList)

@[expose] noncomputable def prootOK (nodes : Array NodeP) (cN : Array ArrCertP) (u : Nat) (j : Nat) :
    Bool :=
  !(Nat.beq (pc n w u u) (pid n w)) || Nat.beq u (pid n w) ||
    (Nat.blt j nodes.size &&
      ((List.range nodes[j]!.basis.size).all fun k =>
        Nat.beq nodes[j]!.basis[k]! u || Nat.beq nodes[j]!.basis[k]! (pid n w)) && pmem cN[j]! u)

structure PerfWP where
  pw : List (List Nat)
  comms : List (Nat × Nat)
  genQ : List (List Nat)
  x : Nat
  k : Nat
  conjs : List Nat
  genR : List (List Nat)
  e : Nat
  g : Nat
deriving Inhabited

@[expose] def plettersLt (m : Nat) (ws : List (List Nat)) : Bool :=
  ws.all fun wd => wd.all fun i => Nat.blt i m

@[expose] noncomputable def pword (gs : Array Nat) (wd : List Nat) : Nat :=
  pprod n w (wd.map fun i => gs[i]!)

@[expose] noncomputable def pwitOK2 (ps : List Nat) (inX outX : Nat → Bool)
    (allowPW allowInX allowU : Bool) (basis : Array Nat) (cE : ArrCertP) (cs : Array ArrCertP)
    (pf : PerfWP) : WitP → Bool
  | .perfect gens _ _ _ _ _ _ =>
    let gs := (gens.map fun l => ppow n w (pgamma n w l.1) l.2).toArray
    let pts := (pf.pw.map (pword n w gs)).toArray
    let qs := (pf.comms.map fun ij => pcomm n w pts[ij.1]! pts[ij.2]!).toArray
    let xa := pts[pf.x]!
    let rs := (pf.conjs.map fun p => pconj n w pts[p]! (pc n w xa xa)).toArray
    allowPW && gens.all (fun l => l.1.all (GFacP.ok n w inX basis)) &&
      plettersLt gs.size pf.pw && ((List.range pts.size).all fun j => pvalid n w pts[j]!) &&
      pf.comms.all (fun ij => Nat.blt ij.1 pts.size && Nat.blt ij.2 pts.size) &&
      plettersLt qs.size pf.genQ &&
      ((List.range gs.size).all fun i => Nat.beq gs[i]! (pword n w qs (pf.genQ.getD i []))) &&
      Nat.blt pf.x pts.size && Nat.beq (ppow n w xa (2 ^ pf.k)) (pid n w) &&
      pf.conjs.all (fun p => Nat.blt p pts.size) && plettersLt rs.size pf.genR &&
      ((List.range gs.size).all fun i => Nat.beq gs[i]! (pword n w rs (pf.genR.getD i []))) &&
      Nat.blt pf.g pts.size && !(pcommA n w (pmask n w basis pf.e) pts[pf.g]!)
  | wt => pwitOK n w ps inX outX allowPW allowInX allowU basis cE cs wt

@[expose] noncomputable def pnodeOK2 (ps : List Nat) (inX outX : Nat → Bool)
    (allowPW allowInX allowU : Bool) (cS : ArrCertP) (nodes : Array NodeP)
    (cN : Array ArrCertP) (wcs : Array (Array ArrCertP)) (pfs : Array PerfWP) (i : Nat) : Bool :=
  penumOK n w nodes[i]!.basis ps cN[i]! &&
    pwitOK2 n w ps inX outX allowPW allowInX allowU nodes[i]!.basis cN[i]! wcs[i]! pfs[i]!
      nodes[i]!.wit &&
    (nodes[i]!.wit.isMono || walkAll (fun u c =>
      !(Nat.beq (pc n w u u) (pid n w)) ||
        !((List.range nodes[i]!.basis.size).all fun k => pcommA n w u nodes[i]!.basis[k]!) ||
        pmem cN[i]! u || pchildOK n w nodes cN i u c) cS.pts.toList nodes[i]!.children.toList)

@[expose] def pinXL (xs : Array Nat) (P : Nat) : Bool := xs.toList.any (Nat.beq P)

@[expose] noncomputable def pxsOK (gens xs : Array Nat) (ws : List (List Nat)) : Bool :=
  (List.range xs.size).all fun k => (ws.getD k []).all (fun i => Nat.blt i gens.size) &&
    Nat.beq xs[k]! (pprod n w ((ws.getD k []).map fun i => gens[i]!))

@[expose] noncomputable def pcN (nodes : Array NodeP) : Array ArrCertP :=
  nodes.map fun nd => pmaskCert n w nd.basis

end Checks

end CFSG.KC.Census
