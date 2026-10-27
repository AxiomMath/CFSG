module

public import Certificates.Data.Kernel.Census.PackedConj
public import Certificates.Data.Kernel.SporSch.PairJ3Cnt

public section

namespace CFSG.KC.HeConj

open CFSG.KC.Enum CFSG.KC.Census CFSG.KS CFSG.KS.Raw CFSG.KS.SporSch

structure GF where
  t : Nat
  c₁ : Nat
  c₁i : Nat
  c₂ : Nat
  c₂i : Nat
deriving Inhabited

structure CF where
  x₁ : Nat
  x₁i : Nat
  x₂ : Nat
  x₂i : Nat
deriving Inhabited

inductive HW where
  | small
  | order4 (e : Nat) (gf : List GF) (m Y : Nat)
  | closing (s t v c ci kc : Nat) (gens : List (List CF × Nat)) (G GI : List Nat)
      (perf : List (List (List Nat × List Nat))) (sw : List Nat)
deriving Inhabited

structure HeD where
  xs : List Nat
  rs : List Nat
  cjs : List (List Nat)
  bs : List (Nat × Nat)
  us : Array Nat
  im : List Nat
  wt : List Nat
  cm : List Nat
  cs : Array Nat
  ci : Array Nat
  roots : List (Nat × Nat)
  nb : Array (Array Nat)
  nm : Array (List Nat)
  ents : Array (List (Nat × Nat × Nat))
  wits : Array HW
  ks : List Nat
  dl : List Nat
  fl : List Nat
  xf : List Nat
deriving Inhabited

section Delta

variable (n w : Nat)

@[expose] def canonP (P : Nat) : Bool := Nat.beq (Nat.shiftRight P (n * w)) 0

@[expose] noncomputable def canonD (d : HeD) : Bool :=
  d.xs.all (fun P => canonP n w P && pvalid n w P) &&
    d.us.toList.all (fun P => canonP n w P && pvalid n w P) &&
    d.cs.toList.all (fun P => canonP n w P && pvalid n w P) &&
    d.ci.toList.all (fun P => canonP n w P && pvalid n w P) &&
    d.nb.toList.all (fun b => b.toList.all fun P => canonP n w P && pvalid n w P)

@[expose] def bpar : List Nat → Nat → Nat
  | f :: fl, m => Nat.mod (Nat.add (bif Nat.beq (Nat.mod m 2) 1 then f else 0)
      (bpar fl (Nat.div m 2))) 2
  | [], _ => 0

@[expose] noncomputable def inNode (xs : List Nat) (c : ArrCertP) (m : Nat) : Bool :=
  pmem c (ppcA n w xs m)

@[expose] noncomputable def isInv (xs : List Nat) (m : Nat) : Bool :=
  !(Nat.beq (ppcA n w xs m) (pid n w)) &&
    Nat.beq (pc n w (ppcA n w xs m) (ppcA n w xs m)) (pid n w)

@[expose] noncomputable def notOne (xs : List Nat) (m : Nat) : Bool :=
  !(Nat.beq (ppcA n w xs m) (pid n w))

@[expose] noncomputable def wit32OK (xs : List Nat) (c : ArrCertP) : HW → Bool
  | .small => Nat.blt c.pts.size 4
  | .order4 e gf _ _ => inNode n w xs c e && isInv n w xs e &&
      gf.all fun f => inNode n w xs c f.t && notOne n w xs f.t
  | .closing s t v .. => inNode n w xs c s && notOne n w xs s && inNode n w xs c t &&
      notOne n w xs t && inNode n w xs c v && isInv n w xs v

@[expose] noncomputable def node32OK (d : HeD) (cN : Array ArrCertP) (i : Nat) : Bool :=
  penumOK n w d.nb[i]! d.ks cN[i]! && Nat.beq (d.nm[i]!).length d.nb[i]!.size &&
    ((d.nm[i]!).zip d.nb[i]!.toList).all (fun mb => Nat.beq (ppcA n w d.xs mb.1) mb.2) &&
    wit32OK n w d.xs cN[i]! d.wits[i]! &&
    match d.wits[i]! with
    | .order4 .. => true
    | .small => pentsOK n w d.nb cN d.us d.cs d.ci d.ents[i]! i
    | .closing .. => (d.nm[i]!).all (fun m => Nat.beq (bpar d.fl m) 0) &&
        pentsOK n w d.nb cN d.us d.cs d.ci d.ents[i]! i

@[expose] noncomputable def cN2 (d : HeD) : Array ArrCertP := d.nb.map (pmaskCert n w)

@[expose] noncomputable def tree32OK (d : HeD) : Bool :=
  canonD n w d && ppcOK n w d.xs d.rs d.cjs d.bs && pinvOK n w d.xs d.us d.im d.wt &&
    ptabOK n w d.xs d.cm d.cs d.ci && Nat.beq d.roots.length d.us.size &&
    (d.us.toList.zip d.roots).all (fun ur => prootOKC n w d.nb (cN2 n w d) d.cs d.ci ur.1 ur.2) &&
    Nat.beq d.nm.size d.nb.size && Nat.beq d.wits.size d.nb.size &&
    Nat.beq d.ents.size d.nb.size && d.ks.all (fun p => Nat.blt p n)

@[expose] noncomputable def nodes32OK (d : HeD) (is : List Nat) : Bool :=
  is.all (node32OK n w d (cN2 n w d))

end Delta

section Base

variable (nfv : Nat → Bool) (nfp : Nat → Nat → Nat) (uf : Nat → Nat) (bs : List Nat)

@[expose] noncomputable def xp (f F x : Nat) : Nat :=
  strictN (nfp F x) fun y => nIf(Nat.beq f 1, uf y, y)

@[expose] noncomputable def bpcAt : List Nat → List Nat → Nat → Nat → Nat
  | f :: fl, F :: xf, m, x => strictN (bpcAt fl xf (Nat.div m 2) x) fun y =>
      nIf(Nat.beq (Nat.mod m 2) 1, xp nfp uf f F y, y)
  | _, _, _, x => x

@[expose] noncomputable def eqB (f g : Nat → Nat) : Bool := eqOnL bs f g

@[expose] noncomputable def idB (f : Nat → Nat) : Bool := eqOnL bs f fun x => x

@[expose] noncomputable def brelOK (f F : Nat) (fl xf : List Nat) :
    List Nat → List Nat → List Nat → Bool
  | fy :: fys, Fy :: Fys, c :: cs =>
    Nat.beq fy (bpar fl c) &&
      eqB bs (fun x => strictN (xp nfp uf f F x) (xp nfp uf fy Fy))
        (fun x => strictN (bpcAt nfp uf fl xf c x) (xp nfp uf f F)) &&
      brelOK f F fl xf fys Fys cs
  | [], [], [] => true
  | _, _, _ => false

@[expose] noncomputable def bpcOK : List Nat → List Nat → List Nat → List (List Nat) → Bool
  | f :: fl, F :: xf, r :: rs, c :: cs =>
    nfv F && Nat.blt f 2 && Nat.beq (bpar fl r) 0 &&
      eqB bs (fun x => strictN (xp nfp uf f F x) (xp nfp uf f F)) (bpcAt nfp uf fl xf r) &&
      brelOK nfp uf bs f F fl xf fl xf c && bpcOK fl xf rs cs
  | [], [], _, _ => true
  | _, _, _, _ => false

@[expose] def distinct : List Nat → Bool
  | a :: l => !(l.any (Nat.beq a)) && distinct l
  | [] => true

@[expose] noncomputable def deltaOK (n w : Nat) (dl : List Nat) (X f F : Nat) : Bool :=
  (List.range n).all fun j => Nat.beq (xp nfp uf f F (dl.getD j 0)) (dl.getD (at' w X j) 0)

@[expose] noncomputable def bridgeOK (N n w : Nat) (d : HeD) : Bool :=
  Nat.beq d.dl.length n && d.dl.all (fun p => Nat.blt p N) && distinct d.dl &&
    Nat.beq d.fl.length d.xs.length && Nat.beq d.xf.length d.xs.length &&
    ((d.xs.zip (d.fl.zip d.xf)).all fun t => deltaOK nfp uf n w d.dl t.1 t.2.1 t.2.2) &&
    bpcOK nfv nfp uf bs d.fl d.xf d.rs d.cjs

@[expose] noncomputable def cmp (a ai b bi : Nat → Nat) (x : Nat) : Nat :=
  strictN (strictN (bi x) ai) (fun y => a (strictN y b))

@[expose] noncomputable def prodP (fs : List (Nat → Nat)) (x : Nat) : Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun x => x) (fun f _ ih x => strictN (ih x) f) fs x

@[expose] noncomputable def pairOK (F FI : Nat) : Bool :=
  nfv F && nfv FI && idB bs (fun x => strictN (nfp FI x) (nfp F))

@[expose] noncomputable def commB (F : Nat) (g : Nat → Nat) : Bool :=
  eqB bs (fun x => strictN (g x) (nfp F)) (fun x => strictN (nfp F x) g)

@[expose] noncomputable def GF.val (f : GF) : Nat → Nat :=
  cmp (nfp f.c₁) (nfp f.c₁i) (nfp f.c₂) (nfp f.c₂i)

@[expose] noncomputable def GF.inv (f : GF) : Nat → Nat :=
  cmp (nfp f.c₂) (nfp f.c₂i) (nfp f.c₁) (nfp f.c₁i)

@[expose] noncomputable def CF.val (f : CF) : Nat → Nat :=
  cmp (nfp f.x₁) (nfp f.x₁i) (nfp f.x₂) (nfp f.x₂i)

@[expose] def lettersLt (m : Nat) (wd : List Nat) : Bool := wd.all fun j => Nat.blt j m

@[expose] def invW (wd : List Nat) : List Nat := (wd.map fun j => Nat.xor j 1).reverse

@[expose] noncomputable def gw (G GI : List Nat) (wd : List Nat) : Nat → Nat :=
  prodP (wd.map fun j => nfp (bif Nat.beq (Nat.mod j 2) 0 then G.getD (Nat.div j 2) 0
    else GI.getD (Nat.div j 2) 0))

variable (fl xf : List Nat)

@[expose] noncomputable def ep (m : Nat) : Nat → Nat := bpcAt nfp uf fl xf m

@[expose] noncomputable def GF.ok (f : GF) : Bool :=
  pairOK nfv nfp bs f.c₁ f.c₁i && pairOK nfv nfp bs f.c₂ f.c₂i &&
    commB nfp bs f.c₁ (ep nfp uf fl xf f.t) && commB nfp bs f.c₂ (ep nfp uf fl xf f.t)

@[expose] noncomputable def CF.ok (bm : List Nat) (f : CF) : Bool :=
  pairOK nfv nfp bs f.x₁ f.x₁i && pairOK nfv nfp bs f.x₂ f.x₂i &&
    bm.all fun m => commB nfp bs f.x₁ (ep nfp uf fl xf m) && commB nfp bs f.x₂ (ep nfp uf fl xf m)

@[expose] noncomputable def hwOK (bm : List Nat) : HW → Bool
  | .small => true
  | .order4 e gf m Y =>
    let gam := prodP (gf.map (GF.val nfp))
    let gami := prodP (gf.reverse.map (GF.inv nfp))
    let y : Nat → Nat := fun x =>
      strictN (strictN (gami x) (ep nfp uf fl xf e)) fun z => ep nfp uf fl xf e (gam z)
    gf.all (GF.ok nfv nfp uf bs fl xf) && nfv Y && eqB bs (nfp Y) (powF y m) &&
      idB bs (powF (nfp Y) 4) && !(idB bs (powF (nfp Y) 2))
  | .closing s t v c ci kc gens G GI perf sw =>
    pairOK nfv nfp bs c ci && commB nfp bs c (ep nfp uf fl xf t) &&
      idB bs (powF (nfp c) (2 ^ kc)) &&
      eqB bs (fun x => strictN (strictN (nfp ci x) (ep nfp uf fl xf v)) fun z =>
        ep nfp uf fl xf v (nfp c z)) (ep nfp uf fl xf s) &&
      Nat.beq G.length gens.length && Nat.beq GI.length gens.length &&
      Nat.beq perf.length gens.length &&
      (List.range gens.length).all (fun j =>
        pairOK nfv nfp bs (G.getD j 0) (GI.getD j 0) &&
          ((gens.getD j ([], 0)).1.all (CF.ok nfv nfp uf bs fl xf bm)) &&
          eqB bs (nfp (G.getD j 0))
            (powF (prodP ((gens.getD j ([], 0)).1.map (CF.val nfp))) (gens.getD j ([], 0)).2) &&
          ((perf.getD j []).all fun ab =>
            lettersLt (2 * G.length) ab.1 && lettersLt (2 * G.length) ab.2) &&
          eqB bs (nfp (G.getD j 0)) (prodP ((perf.getD j []).map fun ab =>
            cmp (gw nfp G GI ab.1) (gw nfp G GI (invW ab.1)) (gw nfp G GI ab.2)
              (gw nfp G GI (invW ab.2))))) &&
      lettersLt (2 * G.length) sw && eqB bs (ep nfp uf fl xf s) (gw nfp G GI sw)

@[expose] noncomputable def wits8330OK (d : HeD) (is : List Nat) : Bool :=
  is.all fun i => hwOK nfv nfp uf bs d.fl d.xf (d.nm[i]!) (d.wits[i]!)

end Base

@[expose] noncomputable def heConjOK (N n w : Nat) (bs : List Nat) (nfv : Nat → Bool)
    (nfp : Nat → Nat → Nat) (uf : Nat → Nat) (d : HeD) : Bool :=
  tree32OK n w d && nodes32OK n w d (List.range d.nb.size) &&
    bridgeOK nfv nfp uf bs N n w d && wits8330OK nfv nfp uf bs d (List.range d.nb.size)

end CFSG.KC.HeConj

end
