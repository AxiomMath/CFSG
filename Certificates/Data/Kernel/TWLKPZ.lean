module

public import Certificates.Data.Kernel.TWLK

public section

namespace Certificates.TWLK

open Certificates.DepASmall Certificates.TwoDepSmall Certificates.TwoDepSmallLow

set_option compiler.extract_closed false

abbrev KPZ := (Nat × List (Nat × List Nat) × List (Nat × List Nat × List Nat) × List Nat) ×
  List (List (List Nat) × List (Nat × Nat)) × List Nat

@[expose] def kZ0 : KPZ := ((0, [], [], []), [], [])

@[expose] def kPZTest (p N pos : Nat) (news : List GGDepANPair) (y : List Nat) (e : KPZ) : Bool :=
  let w : GGTWLPZ := ⟨e.1.1, e.1.2.1, e.1.2.2.1, e.1.2.2.2⟩
  let d := N - 1
  let G := N - 1 + news.length
  let z := ggTWNAdd p (ggTWNX N) (ggDepANSmul p w.c0 y)
  let fixP : List GGDepANPair := w.fixs.map fun e => ggTWNWord p N news (ggTWNGen p N news e.1) e.2
  let orbP : List GGDepANPair := w.orbs.map fun e =>
    e.2.2.foldr (fun k acc => ggDepANConj p acc (fixP.getD k ([], [])))
      (ggTWNWord p N news (ggTWNGen p N news e.1) e.2.1)
  let T := (w.hg.map fun j => orbP.getD j ([], [])).map (ggTWLMatOfPair p d)
  let subs := e.2.1
  let K := subs.foldl (fun k s => Nat.lcm k (s.2.length + 1)) 1
  let a := ggTWLWordMat p d T e.2.2
  decide (0 < w.c0) && decide (w.c0 < p) &&
    w.fixs.all (fun e => decide (e.1 < G) && e.2.all fun g => decide (g < G)) &&
    w.orbs.all (fun e => ggTWNInJ N pos e.1 && e.2.1.all (fun g => ggTWNInJ N pos g) &&
      e.2.2.all fun k => decide (k < fixP.length)) &&
    w.hg.all (fun j => decide (j < orbP.length)) &&
    fixP.all (fun s => ggDepANDot p s.2 z % p == 0) &&
    subs.all (fun s => s.1.all (fun u => u.all fun j => decide (j < T.length)) &&
      ggTWLEnumOK p d (s.1.map (ggTWLWordMat p d T)) s.2) &&
    e.2.2.all (fun j => decide (j < T.length)) &&
    ggTWLPZArith N K (!ggTWLMatEq p a (ggTWLMatOne d) &&
      T.all fun t => ggTWLMatEq p (ggTWLMatMul p d a t) (ggTWLMatMul p d t a))

@[expose] def kRTPZ (p N : Nat) (H : List KHK) (Z : List KPZ) (pos : Nat)
    (news : List GGDepANPair) (kind k : Nat) : Bool :=
  if kind = 1 then kHKTest p N pos news (ggTWLY0 p N pos news) (H.getD k kH0)
  else if kind = 2 then kPZTest p N pos news (ggTWLY0 p N pos news) (Z.getD k kZ0)
  else false

end Certificates.TWLK

end
