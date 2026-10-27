module

public import Certificates.Data.Item434D42
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanChevOuterFrob

public section

namespace CFSG.StandardType.TriD4TwoRow

open CFSG.RankThree.PartTwo.Sec4.Item434D42 CFSG.Monster.B.Co2.Native CFSG.Certificates.Native
  CFSG.RankThree.Native CFSG.Monster.B.Fischer CFSG.Monster.B.Mathieu CFSG.Quasithin
  CFSG.AGLEmbedding.ChevOuter

@[expose] def rowHex : String := include_str "TriD4TwoRow.txt"

@[expose] def rowArr (k : ℕ) : Array ℕ := hexTable 3 2457 (2457 * k) rowHex

@[expose] def f0Arr (_ : Unit := ()) : Array ℕ := rowArr 0

@[expose] def invArr (_ : Unit := ()) : Array (Array ℕ) :=
  Array.ofFn fun j : Fin 48 => rowArr (1 + j.val)

@[expose] def witArr (_ : Unit := ()) : Array (Array ℕ) :=
  Array.ofFn fun j : Fin 4 => rowArr (49 + j.val)

@[expose] def bData : Array (ℕ × ℕ × ℕ) :=
  #[(1, 3, 5), (1, 4, 5), (1, 13, 17), (1, 16, 5), (1, 18, 17), (1, 40, 52), (1, 43, 17),
    (1, 45, 52), (1, 47, 52), (1, 51, 5)]

@[expose] def x0Fix : ℕ := 11

@[expose] def frobCode (v : Array ℕ) : Array ℕ := v.map fun c => GF8.mulNat c c

@[expose] def lineKeyIdx (_ : Unit := ()) : Std.HashMap ℕ ℕ :=
  (List.range lineCert.pts.size).foldl (fun m i => m.insert (keyV lineCert.pts[i]!) i) {}

@[expose] def phiArr (_ : Unit := ()) : Array ℕ :=
  let m := lineKeyIdx ()
  lineCert.pts.map fun v => (m.get? (keyV (frobCode v))).getD 2457

@[expose] def phiInvArr (_ : Unit := ()) : Array ℕ :=
  let φ := phiArr ()
  compA 2457 φ φ

@[expose] def modelOK (φ : Array ℕ) : Bool :=
  isInvA 2457 φ (compA 2457 φ φ) &&
    allLt 18 fun k =>
      eqA 2457 (compA 2457 φ (piArr lineCert k)) (compA 2457 (piArr lineCert (sg k)) φ)

@[expose] def modelCheck (_ : Unit := ()) : Bool := modelOK (phiArr ())

@[expose] def s0Gens (_ : Unit := ()) : Array (Array ℕ) := d4QGens.push (f0Arr ())

@[expose] def s0Cert (_ : Unit := ()) : ArrCert := enumBfs 2457 (s0Gens ()) d4Keys 300

@[expose] def siftP (g : Array ℕ) : Bool := siftA 2457 d4LevelsA d4ChainABaseArr 0 g

@[expose] def isIdA (a : Array ℕ) : Bool := eqA 2457 a (idA 2457)

@[expose] def commuteA (a b : Array ℕ) : Bool := eqA 2457 (compA 2457 a b) (compA 2457 b a)

@[expose] def cubeA (a : Array ℕ) : Array ℕ := compA 2457 a (compA 2457 a a)

@[expose] def liftOK (f φi : Array ℕ) (gs : Array (Array ℕ)) (c : ArrCert)
    (T : Array (Array ℕ)) : Bool :=
  validA 2457 f && siftP (compA 2457 f φi) && enumOK 2457 gs d4Keys c && c.pts.size == 243 &&
    allLt T.size (fun j => validA 2457 T[j]! && siftP T[j]! &&
      isIdA (compA 2457 T[j]! T[j]!) && !isIdA T[j]!) &&
    allLt 243 fun i => siftP c.pts[i]! || !isIdA (cubeA c.pts[i]!) || T.any (commuteA c.pts[i]!)

@[expose] def liftCheck (_ : Unit := ()) : Bool :=
  liftOK (f0Arr ()) (phiInvArr ()) (s0Gens ()) (s0Cert ()) (invArr ())

@[expose] def spanA (u v z : Array ℕ) : Array (Array ℕ) := Array.ofFn fun p : Fin 27 =>
  compA 2457 (compA 2457 (powArr 2457 u (p.val / 9)) (powArr 2457 v (p.val / 3 % 3)))
    (powArr 2457 z (p.val % 3))

@[expose] def inQA (a : Array ℕ) : Bool := d4QCert.pts.any fun q => eqA 2457 q a

@[expose] def noFixA (a : Array ℕ) : Bool := allLt 2457 fun x => a[x]! != x

@[expose] def normA (S : Array (Array ℕ)) (n : Array ℕ) (gens : List (Array ℕ)) : Bool :=
  gens.all fun x => S.any (eqA 2457 (conjA 2457 n x))

@[expose] def bOK (W : Array (Array ℕ)) (u v z : Array ℕ) (S : Array (Array ℕ)) : Bool :=
  commuteA u v && commuteA u z && commuteA v z && isIdA (cubeA u) && isIdA (cubeA v) &&
    isIdA (cubeA z) &&
    allLt 27 fun p => !inQA S[p]! || isIdA S[p]! || noFixA S[p]! ||
      W.any fun n => validA 2457 n && siftP n && normA S n [u, v, z] &&
        !eqA 2457 (conjA 2457 n S[p]!) S[p]! &&
        !eqA 2457 (conjA 2457 n S[p]!) (compA 2457 S[p]! S[p]!)

@[expose] def tripleOK (inQ ord3 : Array Bool) (comm memB : Array (Array Bool)) (nb i j k : ℕ) :
    Bool :=
  inQ[k]! || !ord3[k]! || !(comm[i]!)[k]! || !(comm[j]!)[k]! ||
    (List.range nb).any fun m => (memB[i]!)[m]! && (memB[j]!)[m]! && (memB[k]!)[m]!

@[expose] def fieldOK (pts : Array (Array ℕ)) (bs : Array (ℕ × ℕ × ℕ))
    (W : Array (Array ℕ)) : Bool :=
  let inQ := pts.map inQA
  let ord3 := pts.map fun a => !isIdA a && isIdA (cubeA a)
  let comm := pts.map fun a => pts.map (commuteA a)
  let spans := bs.map fun b => spanA pts[b.1]! pts[b.2.1]! pts[b.2.2]!
  let memB := pts.map fun a => spans.map fun S => S.any (eqA 2457 a)
  (allLt bs.size fun m => bOK W pts[bs[m]!.1]! pts[bs[m]!.2.1]! pts[bs[m]!.2.2]! spans[m]!) &&
    allLt pts.size fun i => !(inQ[i]! && ord3[i]!) || allLt pts.size fun j =>
      !(inQ[j]! && ord3[j]!) || !(comm[i]!)[j]! || eqA 2457 pts[j]! pts[i]! ||
        eqA 2457 pts[j]! (compA 2457 pts[i]! pts[i]!) ||
        allLt pts.size fun k => tripleOK inQ ord3 comm memB bs.size i j k

@[expose] def fieldCheck (_ : Unit := ()) : Bool :=
  fieldOK (s0Cert ()).pts bData (witArr ()) && (d4Lines[0]!)[x0Fix]! == x0Fix

end CFSG.StandardType.TriD4TwoRow
