module

public import CFSG.RankThree.PartOne.KS.PKit
public import CFSG.RankThree.PartTwo.Sec4.Census.CoverCenterThreeRestCover
public import CFSG.RankThree.PartOne.KS.PKitLines

public section

namespace CFSG.RankThree.PartTwo.KFacts.K426

open CFSG.Monster.B.Co2.Native CFSG.Certificates.Native CFSG.Monster.B.Mathieu
  CFSG.Monster.B.Fischer CFSG.RankThree.Native

@[expose] def linesOK3 (p N r n : ℕ) (gs : Array (Array ℕ)) (ps : List ℕ) (c : ArrCert)
    (xs : Array (Array ℕ)) : Bool :=
  enumOK n gs ps c && c.pts.size == N &&
    allLt N (fun k => !(eqA n (powArr n c.pts[k]! p) (idA n)) || eqA n c.pts[k]! (idA n) ||
      (List.range r).any fun j => (List.range p).any fun e =>
        eqA n c.pts[k]! (powArr n xs[j]! e)) &&
    allLt r (fun j => validA n xs[j]! && eqA n (powArr n xs[j]! p) (idA n))

@[expose] def transOK2 (r n : ℕ) (H X L : Array (Array ℕ)) (rec : List ℕ) (RL : Array Level)
    (Rb : Array ℕ) : Bool :=
  allLt r fun j => validA n H[j]! && siftA n RL Rb 0 H[j]! &&
    eqA n (conjA n H[j]! X[rec.getD j 0]!) L[j]!

@[expose] def derivedLeOK (n : ℕ) (gC gD : Array (Array ℕ)) (ps : List ℕ) (cD : ArrCert)
    (M : ℕ) : Bool :=
  enumOK n gD ps cD && cD.pts.size == M &&
    allLt gC.size (fun k => allLt gD.size fun l =>
      cD.pts.toList.any (eqA n (conjA n gC[k]! gD[l]!))) &&
    allLt gC.size (fun k => allLt gC.size fun l =>
      cD.pts.toList.any (eqA n (commutatorA n gC[k]! gC[l]!)))

@[expose] def evalWA {m : ℕ} (n : ℕ) (gs : Array (Array ℕ)) : List (Fin m × Bool) → Array ℕ
  | [] => idA n
  | x :: w => compA n (if x.2 then gs[x.1.val]! else invCand n gs[x.1.val]!) (evalWA n gs w)

@[expose] def wordsOneOK {m : ℕ} (n : ℕ) (gs : Array (Array ℕ)) (ws : List (List (Fin m × Bool))) :
    Bool :=
  allLt gs.size (fun k => validA n gs[k]!) && ws.all fun w => eqA n (evalWA n gs w) (idA n)

@[expose] def detOK {m : ℕ} (n : ℕ) (gs : Array (Array ℕ)) (g : Array ℕ)
    (wu wv : List (Fin m × Bool)) (β : ℕ) : Bool :=
  let u := evalWA n gs wu
  let v := evalWA n gs wv
  validA n g && eqA n (conjA n g u) v && eqA n (conjA n g v) (compA n u (powArr n v β)) &&
    eqA n (compA n u v) (compA n v u)

end CFSG.RankThree.PartTwo.KFacts.K426
