module

public import Certificates.Data.K426Checks

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.B3S3

open CFSG.Monster.B.Co2.Native CFSG.Certificates.Native CFSG.Monster.B.Mathieu
  CFSG.Monster.B.Fischer CFSG.RankThree.Native CFSG.RankThree.PartOne
  CFSG.RankThree.PartTwo.KFacts.K426

@[expose] def hexDigit (c : Char) : ℕ :=
  if '0' ≤ c ∧ c ≤ '9' then c.toNat - 48 else c.toNat - 87

@[expose] def hexArrs (n w : ℕ) (s : String) : Array (Array ℕ) :=
  let cs : Array ℕ := (s.toList.map hexDigit).toArray
  Array.ofFn (n := cs.size / (w * n)) fun k => Array.ofFn (n := n) fun i =>
    (List.range w).foldl (fun acc d => acc * 16 + cs[(k * n + i.val) * w + d]!) 0

structure Crit where
  mode : ℕ
  a : ℕ
  b : ℕ
  qs : List ℕ
  rs : List ℕ
deriving Inhabited

structure Case where
  S : Array (Array ℕ)
  W : Array (List ℤ)
  base : Array ℕ
  rels : List (ℕ × ℕ × ℕ)
  gens : Array (Array ℕ)
  card : ℕ
  crit : Crit
deriving Inhabited

structure Data where
  n : ℕ
  A : Array ℕ
  B : Array ℕ
  QGens : Array (Array ℕ)
  ord : ℕ
  k3 : ℕ
  m3 : ℕ
  N3 : ℕ
  lines : Array (Array ℕ)
  trans : Array (Array ℕ)
  recs : List ℕ
  caseX : Array (Array ℕ)
  cases : Array Case
deriving Inhabited

@[expose] def convProdOK (n : ℕ) (pts : Array (Array ℕ)) (qs rs : List ℕ) : Bool :=
  allLt pts.size fun i =>
    !(qs.any fun q => eqA n (powArr n pts[i]! q) (idA n)) || eqA n pts[i]! (idA n) ||
      (List.range pts.size).any fun j =>
        rs.any fun r =>
          !(eqA n (powArr n (compA n pts[i]! (conjA n pts[j]! pts[i]!)) r) (idA n)) &&
            eqA n (powArr n (powArr n (compA n pts[i]! (conjA n pts[j]! pts[i]!)) r) 3) (idA n)

@[expose] def critOK (n : ℕ) (pts : Array (Array ℕ)) (N : ℕ) (c : Crit) : Bool :=
  if c.mode == 0 then N == 2 ^ c.a * 3 ^ c.b
  else convProdOK n pts c.qs c.rs &&
    (Nat.primeFactorsList N).all fun q => q == 3 || c.qs.contains q

@[expose] def caseOK (D : Data) (k : Case) (x : Array ℕ) : Bool :=
  let cert := enumBfs D.n k.gens k.base.toList (k.card + 1)
  validA D.n D.A && validA D.n D.B && validA D.n x &&
    caseChainOK2P D.n k.S k.base k.W D.A D.B &&
    decide (k.base.toList.Nodup) && decide (∀ q ∈ k.base.toList, q < D.n) &&
    decide (1 ≤ D.n) && decide (2 ≤ k.S.size) &&
    centOKP 3 D.n k.S k.base x k.rels k.gens k.base.toList cert k.card &&
    eqA D.n (powArr D.n x 3) (idA D.n) && critOK D.n cert.pts k.card k.crit

@[expose] def check (D : Data) : Bool :=
  let k0 := D.cases[0]!
  let cert := enumBfs D.n D.QGens k0.base.toList (D.N3 + 1)
  let lev := rawLevels D.n k0.S k0.base
  decide (0 < D.cases.size) &&
    (rawOrbitSizes D.n k0.S k0.base).prod == D.ord && D.ord == 3 ^ D.k3 * D.m3 &&
    decide (D.m3 % 3 ≠ 0) && D.N3 == 3 ^ D.k3 &&
    linesOK3 3 D.N3 D.lines.size D.n D.QGens k0.base.toList cert D.lines &&
    allLt D.QGens.size (fun l => siftA D.n lev k0.base 0 D.QGens[l]!) &&
    transOK2 D.lines.size D.n D.trans D.caseX D.lines D.recs lev k0.base &&
    allLt D.lines.size (fun j => decide (D.recs.getD j 0 < D.cases.size)) &&
    D.caseX.size == D.cases.size &&
    allLt D.cases.size (fun c => caseOK D D.cases[c]! D.caseX[c]!)

end CFSG.HardMathSupport.Solomon.Coordinator.B3S3
