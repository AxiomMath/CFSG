
module

public import Certificates.Data.CFSGNative.H13.J4Class
public meta import Certificates.Data.CFSGNative.H13.J4Class
public import Certificates.Data.CFSGNative.H13.J4Elems
public meta import Certificates.Data.CFSGNative.H13.J4Elems
public import CFSG.Sporadic.Schreier.J4SNative
public meta import CFSG.Sporadic.Schreier.J4SNative
public import CFSG.Sporadic.Schreier.J4SKCentBase
public meta import CFSG.Sporadic.Schreier.J4SKCentBase
public import CFSG.Sporadic.Schreier.J4SOrbitsBase
public meta import CFSG.Sporadic.Schreier.J4SOrbitsBase
public meta import CFSG.Sporadic.Schreier.J4SSylowBase
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.Quasithin.H13.J4

open CFSG.Sporadic.J4Schreier (Pair mulP invP powP oneP wordP An Bn Xn Yn Zn etaP O xColumns
  yColumns xInvColumns yInvColumns powCols wordCols app11)

open CFSG.Quasithin.H13.J4.Native (ClsEnum clsBFS clsOK imCols colsBounded)

@[expose] def uP : Pair := wordP An Bn Native.uLetters

@[expose] def vP : Pair := wordP An Bn Native.vLetters

@[expose] def dP : Pair := mulP (mulP (mulP (invP vP) uP) vP) uP

@[expose] def tP : Pair := powP dP 22

@[expose] def e2Word : List ℤ := [1, 2, 1, 2, 1, -2]

@[expose] def e2P : Pair := powP (wordP Xn Yn e2Word) 6

@[expose] def e3P : Pair := mulP (etaP 1096) Xn

@[expose] def cnjP (g e : Pair) (k : ℕ) : Pair :=
  mulP g (powP (mulP (mulP (mulP (invP g) tP) g) e) k)

@[expose] def conjEqP (c e : Pair) : Bool := O.eq (mulP (mulP (invP c) tP) c).1 e.1

@[expose] def fusionChecks : Bool :=
  conjEqP (cnjP (mulP Bn An) Zn 3) Zn && conjEqP (cnjP (mulP An Bn) e2P 6) e2P &&
    conjEqP (cnjP oneP e3P 6) e3P

@[expose] def lettersOK (w : List ℤ) : Bool :=
  w.all fun l => l == 1 || l == -1 || l == 2 || l == -2

@[expose] def xyPairs : Array (Array ℕ × Array ℕ) :=
  #[(xColumns, xInvColumns), (yColumns, yInvColumns)]

@[expose] def m2Cols : Array ℕ := powCols (wordCols e2Word) 6

@[expose] def cls2 : ClsEnum := clsBFS xyPairs m2Cols 11385

@[expose] def cls3 : ClsEnum := clsBFS xyPairs xColumns 31878

@[expose] def ClsFacts (gens : Array (Array ℕ × Array ℕ)) (M : Array ℕ) (n : ℕ) : Prop :=
  ∃ E : ℕ → Array ℕ, E 0 = M ∧ (∀ i < n, colsBounded (E i) = true) ∧
    (∀ i < n, ∀ j < i, E j ≠ E i) ∧
    (∀ i < n, 0 < i → ∃ p < i, ∃ g < gens.size,
      E i = Native.conjCols (gens[g]!).1 (gens[g]!).2 (E p)) ∧
    ∀ i < n, ∀ g < gens.size, ∃ j < n, E j = Native.conjCols (gens[g]!).2 (gens[g]!).1 (E i)

@[expose] def imOK (C : Array ℕ) (L : List ℕ) : Bool :=
  (List.range 2048).all (fun b => L.contains (b ^^^ app11 C b)) &&
    L.all (fun w => decide (w < 2048) && (List.range 2048).any fun b => b ^^^ app11 C b == w) &&
    decide L.Nodup

end CFSG.Quasithin.H13.J4
