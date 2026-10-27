module

public import Certificates.Data.Kernel.KGC31P
public import Certificates.Data.Kernel.Misc.ArrEnum
public import Certificates.Data.Odd87F3CC

public section

namespace CFSG.KC.Odd87CCK

open CFSG.KC.Enum CFSG.KS CFSG.KC.KGC31P CFSG.KC.Misc.ArrEnum Certificates.Odd87F3

variable (n w : Nat)

@[expose] noncomputable def papK (p i : Nat) : Nat := pg w (mask w) p i

@[expose] noncomputable def pevK (G GI : List Nat) : List ℤ → Nat
  | [] => pidn n w
  | z :: ws =>
    pc n w (if 0 < z then G.getD (z.toNat - 1) (pidn n w) else GI.getD ((-z).toNat - 1) (pidn n w))
      (pevK G GI ws)

@[expose] noncomputable def orbK (o : Orb) (SG NS : List Nat) : Bool :=
  decide (o.base < n) && decide (o.y0 < n) &&
    SG.all (fun T => papK w T o.base == o.base) && NS.all (fun T => papK w T o.base != o.base) &&
    (List.range n).all fun y =>
      !(SG.all (fun T => papK w T y == y) && NS.all (fun T => papK w T y != y)) ||
        y == o.base || y == o.y0

@[expose] noncomputable def ccK (G : List Nat) (orbs : List Orb) (cov : List (ℕ × List ℤ)) : Bool :=
  let GI := G.map (pinv n w)
  G.all (permB n w) &&
    orbs.all (fun o => orbK n w o (o.sg.map (pevK n w G GI)) (o.ns.map (pevK n w G GI))) &&
    (List.range n).all fun v =>
      match cov[v]? with
      | none => false
      | some (i, wd) =>
        match orbs[i]? with
        | none => false
        | some o => decide (o.base < n) && papK w (pevK n w G GI wd) o.base == v

@[expose] def splitSp : List Char → List Char → List (List Char)
  | [], acc => [acc.reverse]
  | c :: cs, acc => if c == ' ' then acc.reverse :: splitSp cs [] else splitSp cs (c :: acc)

@[expose] def wordsL (cs : List Char) : List (List ℤ) :=
  ((splitSp cs []).filter fun t => t.length > 0).map fun t => t.map decodeLetter

@[expose] def covL (cs : List Char) : List (ℕ × List ℤ) :=
  ((splitSp cs []).filter fun t => t.length > 0).map fun t =>
    (t.head!.toNat - 48, t.tail.map decodeLetter)

end CFSG.KC.Odd87CCK
