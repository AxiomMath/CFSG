module

public import CFSG.CGT.Stroth77.NonSplitCore.CertInputs
public import CFSG.Assembly.QuasithinDefs
public import CFSG.Foundations

public section

namespace CFSG.KC.Stroth77NS

open CFSG.CGT.Stroth77.Core

@[expose] def swapAt : ℕ → List ℕ → List ℕ
  | 0, a :: b :: l => b :: a :: l
  | k + 1, a :: l => a :: swapAt k l
  | _, l => l

@[expose] def codeJ : List ℕ → ℕ
  | [] => 0
  | a :: l => a + 6 * codeJ l

@[expose] def edgeJ (l : List ℕ) (k : Fin 5) : ℕ := 5 * codeJ l + k.val

@[expose] def walkJ : List ℕ → List (Letter 5) → List ℕ
  | _, [] => []
  | l, (k, true) :: w => edgeJ l k :: walkJ (swapAt k.val l) w
  | l, (k, false) :: w => edgeJ (swapAt k.val l) k :: walkJ (swapAt k.val l) w

@[expose] def vtxJ (w : List (Fin 5)) : List ℕ :=
  w.foldl (fun l k => swapAt k.val l) [0, 1, 2, 3, 4, 5]

@[expose] def edgesJ (cyc : List (List (Fin 5) × Fin 15)) : List ℕ :=
  cyc.flatMap fun c => walkJ (vtxJ c.1) (rel c.2)

@[expose] def toggleJ (acc : List ℕ) (x : ℕ) : List ℕ :=
  if x ∈ acc then acc.erase x else x :: acc

@[expose] def cycOKw (cs : List (List (List (Fin 5) × Fin 15))) : Bool :=
  cs.all fun cyc => ((edgesJ cyc).foldl toggleJ []).isEmpty

@[expose] def cycOKt : Bool := cycOKw cyclesL

@[expose] def bitZ (r b : ℕ) : ZMod 2 := if r.testBit b then 1 else 0

@[expose] def app4 (gd : ℕ) (u : U4) : ZMod 2 :=
  bitZ gd 0 * u 0 + bitZ gd 1 * u 1 + bitZ gd 2 * u 2 + bitZ gd 3 * u 3

@[expose] def xorRows : List ℕ → List ℕ → List ℕ
  | a :: l, b :: l' => (a ^^^ b) :: xorRows l l'
  | l, [] => l
  | [], l => l

@[expose] def unitRows : ℕ → ℕ → List ℕ
  | 0, r => [r]
  | d + 1, r => 0 :: unitRows d r

@[expose] def selRows (q : ℕ) : List ℕ := [2 ^ (4 * q), 2 ^ (4 * q + 1), 2 ^ (4 * q + 2), 2 ^ (4 * q + 3)]

@[expose] def comb4 (gd : ℕ) (l : List ℕ) : ℕ :=
  (if gd.testBit 0 then l.getD 0 0 else 0) ^^^ (if gd.testBit 1 then l.getD 1 0 else 0) ^^^
    (if gd.testBit 2 then l.getD 2 0 else 0) ^^^ (if gd.testBit 3 then l.getD 3 0 else 0)

@[expose] def mulG (g l : List ℕ) : List ℕ :=
  [comb4 (g.getD 0 0) l, comb4 (g.getD 1 0) l, comb4 (g.getD 2 0) l, comb4 (g.getD 3 0) l]

@[expose] def gRows : List (List ℕ) :=
  [[2, 1, 4, 8], [1, 4, 2, 8], [1, 2, 8, 4], [1, 2, 4, 15], [14, 13, 11, 7]]

abbrev gSpec : Prop := ∀ k : Fin 5, ∀ x0 x1 x2 x3 : ZMod 2, ∀ d : Fin 4,
  actC (sw k) ![x0, x1, x2, x3] d = app4 ((gRows.getD k.val []).getD d.val 0) ![x0, x1, x2, x3]

@[expose] def vRows : List (Fin 5) → ℕ → List ℕ
  | [], q => selRows q
  | k :: w, q => mulG (gRows.getD k.val []) (vRows w q)

@[expose] def cycRows (cyc : List (List (Fin 5) × Fin 15)) : List ℕ :=
  cyc.foldr (fun c acc => xorRows (vRows c.1 c.2.val) acc) []

@[expose] def cycBlocks : List (List ℕ) := cyclesL.map cycRows

@[expose] def sparseRows {p q : ℕ} (l : List (Fin p × Fin 4 × Fin q × Fin 4)) (G : ℕ → List ℕ)
    (k : ℕ) : List ℕ :=
  l.foldr (fun e acc => if e.1.val = k then
    xorRows (unitRows e.2.1.val ((G e.2.2.1.val).getD e.2.2.2.val 0)) acc else acc) []

@[expose] def corrBlk (k : ℕ) : List ℕ := sparseRows corrL selRows k

@[expose] def foxRows : List (Letter 5) → List ℕ
  | [] => []
  | (k, true) :: w => xorRows (corrBlk k.val) (mulG (gRows.getD k.val []) (foxRows w))
  | (k, false) :: w => mulG (gRows.getD k.val []) (xorRows (corrBlk k.val) (foxRows w))

@[expose] def lamRow : ℕ := lamL.foldr (fun e acc => 2 ^ (4 * e.1.val + e.2.val) ^^^ acc) 0

@[expose] def titsN : List ℕ := [3, 6, 12, 8, 15]

abbrev titsSpec : Prop := ∀ p : Fin 15, ∀ d : Fin 4, titsVal p d = bitZ (titsN.getD p.val 0) d.val

@[expose] def lamC (t d : ℕ) : ℕ := if t.testBit d then lamRow else 0

@[expose] def lamBlk (p : ℕ) : List ℕ :=
  [lamC (titsN.getD p 0) 0, lamC (titsN.getD p 0) 1, lamC (titsN.getD p 0) 2,
    lamC (titsN.getD p 0) 3]

@[expose] def lhsBlk (p : ℕ) : List ℕ :=
  xorRows (selRows p) (xorRows (foxRows (relL.getD p [])) (lamBlk p))

@[expose] def rhsBlk (cl : List (Fin 15 × Fin 4 × Fin 34 × Fin 4)) (p : ℕ) : List ℕ :=
  sparseRows cl (fun q => cycBlocks.getD q []) p

@[expose] def norm4 (l : List ℕ) : List ℕ := [l.getD 0 0, l.getD 1 0, l.getD 2 0, l.getD 3 0]

@[expose] def allBelow : ℕ → (ℕ → Bool) → Bool
  | 0, _ => true
  | n + 1, f => f n && allBelow n f

@[expose] def certOKw (cl : List (Fin 15 × Fin 4 × Fin 34 × Fin 4)) : Bool :=
  allBelow 15 fun p => decide (norm4 (lhsBlk p) = norm4 (rhsBlk cl p))

@[expose] def certOKi : Bool := certOKw certL

end CFSG.KC.Stroth77NS
