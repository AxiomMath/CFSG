module

public import Certificates.Data.CFSGNative.J4Tree.Aff
public import Certificates.Data.CFSGNative.J4Tree.Inv
public import Certificates.Data.CFSGNative.J4Tree.Index
public import Std.Data.HashSet

public section

namespace CFSG.J4Tree.Native

open CFSG.ASVolI

set_option compiler.extract_closed false

@[inline, expose] def topBfsPush {α : Type} [BEq α] [Hashable α] (acc : Std.HashSet α × Array α)
    (y : α) : Std.HashSet α × Array α :=
  if acc.1.contains y then acc else (acc.1.insert y, acc.2.push y)

@[specialize, expose] def topBfs {α : Type} [BEq α] [Hashable α] (step : α → List α) :
    Nat → Std.HashSet α → Array α → Nat → Std.HashSet α
  | 0, S, _, _ => S
  | fuel + 1, S, L, i =>
    if h : i < L.size then
      let r := (step L[i]).foldl topBfsPush (S, L)
      topBfs step fuel r.1 r.2 (i + 1)
    else S

@[specialize, expose] def topClosed {α : Type} [BEq α] [Hashable α] (step : α → List α)
    (S : Std.HashSet α) : Bool :=
  S.toList.all fun x => (step x).all S.contains

@[expose] def topFuel : Nat := 4194304

@[expose] def topMulStep (gs : List Code) (x : Code) : List Code := gs.map (x * ·)

@[expose] def topClosure (gs : List Code) : Std.HashSet Code :=
  topBfs (topMulStep gs) topFuel ((∅ : Std.HashSet Code).insert 1) #[1] 0

@[expose] def topConjStep (gp : List (Code × Code)) (t : List Code) : List (List Code) :=
  gp.map fun g => t.map fun r => g.1 * r * g.2

@[expose] def topSetOf (ts : List (List Code)) : Std.HashSet (List Code) :=
  ts.foldl (fun S t => S.insert t) ∅

@[expose] def topOrbit (gp : List (Code × Code)) (ts : List (List Code)) :
    Std.HashSet (List Code) :=
  topBfs (topConjStep gp) topFuel (topSetOf ts) ts.toArray 0

@[expose] def topSetOfCodes (l : List Code) : Std.HashSet Code :=
  l.foldl (fun S r => S.insert r) ∅

inductive TopGen where
  | w (word : List Int)
  | c (c e : Nat)
deriving Inhabited

@[expose] def TopGen.code : TopGen → Code
  | .w l => codeOfWord l
  | .c a e => codeOfCoord a e

@[expose] def topLetterOK (l : Int) : Bool :=
  l == 1 || l == 2 || l == 3 || l == -1 || l == -2 || l == -3

@[expose] def TopGen.valid : TopGen → Bool
  | .w l => l.all topLetterOK
  | .c _ e => decide (e < 1024)

@[expose] def topPair (a : Code) : Code × Code := (a, a.inv)

@[expose] def topPairOK (p : Code × Code) : Bool := p.1 * p.2 == 1 && p.2.wf

@[expose] def topCommutes (a : Code) (bs : List Code) : Bool := bs.all fun b => a * b == b * a

@[expose] def topCoordCodes (l : List (Nat × Nat)) : List Code :=
  l.map fun ce => codeOfCoord ce.1 ce.2

@[expose] def topBasisCodes (k : Nat) : List Code := topCoordCodes (treeBasis k)

structure TopChild where
  y : Nat × Nat
  gensP : List (Nat × Nat)
  orbit : Nat
  orderP : Nat
  target : Nat
  conj : List Int
deriving Inhabited

structure TopNode where
  node : Nat
  N : Nat
  full : List TopGen
  two : List (Nat × Nat)
  orderTwo : Nat
  odd : List (Nat × List (List Int))
  ngens : List (List Int)
  children : List TopChild
  kids : List (Nat × Nat)
deriving Inhabited

@[expose] def TopNode.gens (d : TopNode) : List TopGen :=
  d.full ++ d.two.map (fun ce => TopGen.c ce.1 ce.2) ++ d.odd.flatMap fun o => o.2.map TopGen.w

@[noinline, expose] def topGensOK (bs : List Code) (gens : List TopGen) (gp : List (Code × Code)) :
    Bool :=
  gens.all TopGen.valid && gp.all topPairOK && gp.all fun p => topCommutes p.1 bs

@[noinline, expose] def topSubOK (gs : List Code) (S : Std.HashSet Code) (ord : Nat) : Bool :=
  topClosed (topMulStep gs) S && S.size == ord

@[noinline, expose] def topLagrangeOK (N : Nat) (two : List Code) (P2 : Std.HashSet Code)
    (orderTwo : Nat) (odd : List (Nat × List Code)) : Bool :=
  topSubOK two P2 orderTwo && odd.all (fun o => topSubOK o.2 (topClosure o.2) o.1) &&
    (orderTwo :: odd.map (·.1)).foldr Nat.lcm 1 % N == 0 && N % orderTwo == 0 &&
    N / orderTwo % 2 == 1

@[noinline, expose] def topNormOK (bs : List Code) (Aset : Std.HashSet Code)
    (gp : List (Code × Code)) : Bool :=
  gp.all fun p => bs.all fun b => Aset.contains (p.1 * b * p.2) && Aset.contains (p.2 * b * p.1)

@[expose] def topIsB0 (gP : List Code) (r : Code) : Bool :=
  r * r == 1 && gP.all fun g => r * g == g * r

@[noinline, expose] def topMergeOK (B0 : List Code) (B0s : Std.HashSet Code) (tb : List Code)
    (Sp : Std.HashSet Code) (h hi : Code) : Bool :=
  tb.all (fun b => B0s.contains (h * b * hi)) && B0.all fun r => Sp.contains (hi * r * h)

@[noinline, expose] def topVerdictMergeOK (B0 : List Code) (k : Nat) (h : Code) : Bool :=
  topPairOK (topPair h) &&
    topMergeOK B0 (topSetOfCodes B0) (topBasisCodes k) (topClosure (topBasisCodes k)) h h.inv

@[noinline, expose] def topVerdictOK (B0 : List Code) (c : TopChild) : Bool :=
  if c.target == 0 then decide (64 < (B0.filter Code.inE).length)
  else
    decide (1 ≤ c.target) && decide (c.target ≤ treeN) && c.conj.all topLetterOK &&
      (treeBasis c.target).all (fun ce => decide (ce.2 < 1024)) &&
      topVerdictMergeOK B0 c.target (codeOfWord c.conj)

@[noinline, expose] def topChildPOK (gP : List Code) (P : Std.HashSet Code) (M : Nat)
    (c : TopChild) : Bool :=
  topSubOK gP P c.orderP && M % c.orderP == 0 && M / c.orderP % 2 == 1 &&
    topVerdictOK (P.toList.filter (topIsB0 gP)) c

@[noinline, expose] def topOrbOK (gp : List (Code × Code)) (O : Std.HashSet (List Code))
    (len : Nat) : Bool :=
  topClosed (topConjStep gp) O && O.size == len

@[noinline, expose] def topChildYOK (bs : List Code) (gp : List (Code × Code)) (N : Nat)
    (c : TopChild) (y : Code) (gP : List Code) : Bool :=
  topCommutes y bs && y * y == 1 && topOrbOK gp (topOrbit gp [[y]]) c.orbit && N % c.orbit == 0 &&
    gP.all (fun g => topCommutes g (y :: bs)) && topChildPOK gP (topClosure gP) (N / c.orbit) c

@[expose] def topChildOK (bs : List Code) (gp : List (Code × Code)) (N : Nat) (c : TopChild) :
    Bool :=
  decide (c.y.2 < 1024) && c.gensP.all (fun ce => decide (ce.2 < 1024)) &&
    topChildYOK bs gp N c (codeOfCoord c.y.1 c.y.2) (topCoordCodes c.gensP)

@[noinline, expose] def topCoverOK (S : Array Bool) (Aset : Std.HashSet Code)
    (U : Std.HashSet (List Code)) (P2 : Std.HashSet Code) : Bool :=
  P2.toList.all fun x =>
    !(x * x == 1 && x != 1 && burnsideJ4NP_affine2AWith S x && !Aset.contains x) || U.contains [x]

@[noinline, expose] def topKidTOK (bs : List Code) (gp : List (Code × Code)) (N k : Nat)
    (T : List Code) : Bool :=
  bs.all (topClosure T).contains && topOrbOK gp (topOrbit gp [T]) (N / treeOrd k) &&
    N % treeOrd k == 0 && decide (0 < treeOrd k)

@[noinline, expose] def topKidHOK (bs : List Code) (gp : List (Code × Code)) (N k : Nat)
    (h : Code) : Bool :=
  topPairOK (topPair h) && topKidTOK bs gp N k ((topBasisCodes k).map fun b => h * b * h.inv)

@[expose] def topKidOK (bs : List Code) (gp : List (Code × Code)) (N : Nat)
    (children : List TopChild) (kd : Nat × Nat) : Bool :=
  (children.getD kd.2 default).target == kd.1 && decide (1 ≤ kd.1) &&
    (children.getD kd.2 default).conj.all topLetterOK &&
    (treeBasis kd.1).all (fun ce => decide (ce.2 < 1024)) &&
    topKidHOK bs gp N kd.1 (codeOfWord (children.getD kd.2 default).conj)

@[noinline, expose] def topNodeOKWith (d : TopNode) (S : Array Bool) (bs : List Code)
    (Aset : Std.HashSet Code) (gp ngp : List (Code × Code)) (P2 : Std.HashSet Code)
    (U : Std.HashSet (List Code)) : Bool :=
  d.N == treeOrd d.node && decide (0 < d.N) &&
    (treeBasis d.node).all (fun ce => decide (ce.2 < 1024)) &&
    topGensOK bs d.gens gp &&
    topLagrangeOK d.N (topCoordCodes d.two) P2 d.orderTwo
      (d.odd.map fun o => (o.1, o.2.map codeOfWord)) &&
    d.two.all (fun ce => decide (ce.2 < 1024)) &&
    d.ngens.all (fun w => w.all topLetterOK) && ngp.all topPairOK &&
    topNormOK bs Aset (gp ++ ngp) &&
    d.children.all (topChildOK bs gp d.N) &&
    topCoverOK S Aset U P2 &&
    d.kids.all (topKidOK bs gp d.N d.children)

@[expose] def TopNode.gp (d : TopNode) : List (Code × Code) := d.gens.map fun g => topPair g.code

@[expose] def TopNode.ngp (d : TopNode) : List (Code × Code) :=
  d.ngens.map fun w => topPair (codeOfWord w)

@[expose] def TopNode.cover (d : TopNode) : Std.HashSet (List Code) :=
  topOrbit (d.gp ++ d.ngp) (d.children.map fun c => [codeOfCoord c.y.1 c.y.2])

@[expose] def topNodeOK (d : TopNode) (S : Array Bool) : Bool :=
  topNodeOKWith d S (topBasisCodes d.node) (topClosure (topBasisCodes d.node)) d.gp d.ngp
    (topClosure (topCoordCodes d.two)) d.cover

end CFSG.J4Tree.Native
