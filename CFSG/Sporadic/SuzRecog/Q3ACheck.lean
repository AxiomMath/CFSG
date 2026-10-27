module

public import Certificates.Data.SuzLevelTwoInputs
public import CFSG.Sporadic.SuzOddCore.InvTCheckInputs
public import Certificates.Data.SuzQ3AVtxData

public section

namespace CFSG.Sporadic.SuzRecog.Q3A.Check

open CFSG.Monster.B.Co2.Native CFSG.Sporadic.SuzRecog.LevelTwoData

@[expose] def b0 : Array Nat := CFSG.Sporadic.SuzOddCore.b0Arr

@[expose] def b1 : Array Nat := CFSG.Sporadic.SuzOddCore.b1Arr

@[expose] def b0i : Array Nat := invCand 1782 b0

@[expose] def b1i : Array Nat := invCand 1782 b1

@[expose] def bA (s : Nat) : Array Nat := if s == 0 then b0 else b1

@[expose] def bAi (s : Nat) : Array Nat := if s == 0 then b0i else b1i

@[expose] def x1 : Array Nat := xStrong 0

@[expose] def x2 : Array Nat := xStrong 1

@[expose] def xA (s : Nat) : Array Nat := if s == 0 then x1 else x2

@[expose] def rhoInv : Array Nat := invCand 1782 rhoArr

@[expose] def fix0 : Array Nat := (Array.range 1782).filter fun x => rhoArr[x]! == x

@[expose] def mix (x : Nat) : UInt64 :=
  let z : UInt64 := (x.toUInt64 + 1) * 0x9E3779B97F4A7C15
  let z := (z ^^^ (z >>> 30)) * 0xBF58476D1CE4E5B9
  let z := (z ^^^ (z >>> 27)) * 0x94D049BB133111EB
  z ^^^ (z >>> 31)

@[expose] def wt : Array UInt64 := (Array.range 1782).map mix

@[expose] def keyOf (l : Array Nat) : UInt64 := l.foldl (fun acc x => acc + wt[x]!) 0

@[expose] def imgA (g l : Array Nat) : Array Nat := l.map fun x => g[x]!

@[expose, irreducible] def tpar : Array Nat := hexTable 4 22880 0 Q3AVtxData.tparHex

@[expose, irreducible] def tlab : Array Nat := hexTable 4 22880 0 Q3AVtxData.tlabHex

@[expose] def fimgAt (i : Nat) : Array Nat :=
  if _h : 0 < i ∧ tpar[i]! < i then imgA (bA tlab[i]!) (fimgAt tpar[i]!) else fix0
termination_by i
decreasing_by exact _h.2

@[expose] def fimg : Array (Array Nat) := (Array.range 22880).map fimgAt

@[expose, irreducible] def keyIdx (k : UInt64) : Nat :=
  ((List.range 22880).find? fun i => keyOf fimg[i]! == k).getD 22880

@[expose] def actIdx (g : Array Nat) (i : Nat) : Nat := keyIdx (keyOf (imgA g fimg[i]!))

@[expose] def vertOK : Bool :=
  isInvA 1782 rhoArr rhoInv && fix0.size == 162 &&
    eqA 1782 (compA 1782 rhoArr (compA 1782 rhoArr rhoArr)) (idA 1782) &&
    allLt 2 (fun s => isInvA 1782 (bA s) (bAi s)) &&
    fimg.size == 22880 && tpar.size == 22880 && tlab.size == 22880 && fimg[0]! == fix0 &&
    allLt 22880 fun i => keyIdx (keyOf fimg[i]!) == i &&
      (i == 0 || (tpar[i]! < i && tlab[i]! < 2 &&
        fimg[i]! == imgA (bA tlab[i]!) fimg[tpar[i]!]!))

@[expose] def cArr (i : Nat) : Array Nat :=
  if _h : 0 < i ∧ tpar[i]! < i then compA 1782 (bA tlab[i]!) (cArr tpar[i]!) else idA 1782
termination_by i
decreasing_by exact _h.2

@[expose] def cArrInv (i : Nat) : Array Nat :=
  if _h : 0 < i ∧ tpar[i]! < i then compA 1782 (cArrInv tpar[i]!) (bAi tlab[i]!) else idA 1782
termination_by i
decreasing_by exact _h.2

@[expose] def xTab : Array (Array Nat) :=
  #[(Array.range 22880).map (actIdx x1), (Array.range 22880).map (actIdx x2)]

@[expose, irreducible] def froot : Array Nat := hexTable 4 22880 0 Q3AVtxData.frootHex

@[expose, irreducible] def fpar : Array Nat := hexTable 4 22880 0 Q3AVtxData.fparHex

@[expose, irreducible] def flab : Array Nat := hexTable 4 22880 0 Q3AVtxData.flabHex

@[expose, irreducible] def fdep : Array Nat := hexTable 4 22880 0 Q3AVtxData.fdepHex

@[expose] def forestOK : Bool :=
  allLt 2 (fun s => isInvA 1782 (xA s) (invCand 1782 (xA s)) &&
    eqA 1782 (compA 1782 (xA s) rhoArr) (compA 1782 rhoArr (xA s)) &&
    CFSG.Sporadic.SuzOddCore.inM (xA s)) &&
  froot.size == 22880 && fpar.size == 22880 && flab.size == 22880 && fdep.size == 22880 &&
    allLt 22880 fun i => froot[i]! < 22880 && froot[froot[i]!]! == froot[i]! &&
      (if froot[i]! == i then fdep[i]! == 0
       else fpar[i]! < 22880 && flab[i]! < 2 && fdep[fpar[i]!]! < fdep[i]! &&
         froot[fpar[i]!]! == froot[i]! && (xTab[flab[i]!]!)[fpar[i]!]! == i)

@[expose] def roots : Array Nat := (Array.range 22880).filter fun i => froot[i]! == i

@[expose] def isInvol (g : Array Nat) : Bool :=
  eqA 1782 (compA 1782 g g) (idA 1782) && !eqA 1782 g (idA 1782)

@[expose] def rhoPow (i : Nat) : Array Nat := if i == 1 then rhoArr else compA 1782 rhoArr rhoArr

@[expose] def qArr (r : Nat) : Array Nat := compA 1782 (cArr r) (compA 1782 rhoArr (cArrInv r))

@[expose] def adj0 (r : Nat) : Bool :=
  r != 0 &&
    let q := qArr r
    let q2 := compA 1782 q q
    [1, 2].any fun i => [q, q2].any fun qj => isInvol (compA 1782 (rhoPow i) qj)

@[expose] def adj0Arr : Array Bool := (Array.range 22880).map fun r => froot[r]! == r && adj0 r

@[expose] def isNbr0 (y : Nat) : Bool := y < 22880 && adj0Arr[froot[y]!]!

@[expose] def nbr0 : Array Nat := (Array.range 22880).filter isNbr0

@[expose] def nbrsOf (i : Nat) : Array Nat := nbr0.map (actIdx (cArr i))

@[expose] def nbrOrbOK : Bool := allLt 22880 fun k => !isNbr0 k || froot[k]! == froot[nbr0[0]!]!

@[expose] def adjIdx (i j : Nat) : Bool := isNbr0 (actIdx (cArrInv i) j)

@[expose] def adjWith (ci : Array Nat) (j : Nat) : Bool := isNbr0 (actIdx ci j)

@[expose] def rootDist (r : Nat) : Nat :=
  if r == 0 then 0 else if isNbr0 r then 1 else if (nbrsOf r).any isNbr0 then 2 else 3

@[expose] def distArr : Array Nat := (Array.range 22880).map fun r => if froot[r]! == r then rootDist r else 0

@[expose] def vDist (y : Nat) : Nat := if y < 22880 then distArr[froot[y]!]! else 4

@[expose] def distOK : Bool :=
  roots.all fun r => rootDist r != 3 || (nbrsOf r).any fun y => vDist y == 2

@[expose] def downSet (r : Nat) : Array Nat := (nbrsOf r).filter fun y => vDist y + 1 == rootDist r

@[expose] def spanPin (r : Nat) : Array Nat × Array Nat :=
  if r == 1 then (hexTable 4 18 0 Q3AVtxData.spanHex, hexTable 4 18 18 Q3AVtxData.spanHex)
  else if r == 2 then (hexTable 4 4 36 Q3AVtxData.spanHex, hexTable 4 4 40 Q3AVtxData.spanHex)
  else if r == 202 then
    (hexTable 4 486 44 Q3AVtxData.spanHex, hexTable 4 486 530 Q3AVtxData.spanHex)
  else (#[], #[])

@[expose] def spanCheck (D : Array Nat) (t : Array Nat × Array Nat) : Bool :=
  t.1.size == D.size && t.2.size == D.size &&
    allLt D.size fun b => b == 0 || (t.1[b]! < D.size && t.2[t.1[b]!]! < t.2[b]! &&
      adjIdx D[t.1[b]!]! D[b]!)

@[expose] def spanOK : Bool :=
  roots.all fun r => rootDist r < 2 || spanCheck (downSet r) (spanPin r)

@[expose] def q2At (r : Nat) : Bool :=
  let Cr := ((nbrsOf r).filter isNbr0).map fun c => (c, cArrInv c)
  (nbrsOf r).all fun g => vDist g != 2 ||
    Cr.any (fun cc => adjWith cc.2 g) ||
    (let Cg := (nbrsOf g).filter isNbr0
     Cr.any fun cc => Cg.any fun c' => adjWith cc.2 c')

@[expose] def q2OK : Bool := roots.all fun r => rootDist r != 2 || q2At r

@[expose] def layer3OK : Bool :=
  roots.all fun r => rootDist r != 3 || (nbrsOf r).all fun y => vDist y != 3

@[expose] def q3aOK : Bool :=
  vertOK && forestOK && nbrOrbOK && distOK && spanOK && q2OK && layer3OK

end CFSG.Sporadic.SuzRecog.Q3A.Check
