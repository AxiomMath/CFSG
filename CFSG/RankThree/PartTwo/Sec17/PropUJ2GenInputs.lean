module

public import CFSG.RankThree.PartTwo.Sec4.Sporadic.J2Check45Inputs
public import CFSG.RankThree.PartTwo.Sec4.Sporadic.J2Check3Inputs
public meta import CFSG.RankThree.PartTwo.Sec4.Sporadic.J2Check45Inputs
public meta import CFSG.RankThree.PartTwo.Sec4.Sporadic.J2Check3Inputs

public section

namespace CFSG.RankThree.PartTwo.Sec17.PropU.J2Gen

open CFSG.RankThree.PartTwo.Sec4.Sporadic.J2 CFSG.ComponentClassification.J2Cover
  CFSG.Certificates.Native CFSG.Monster.B.Co2.Native CFSG.RankThree.Native CFSG.Monster.B.Mathieu

@[expose] def vGens : Array (Array ℕ) :=
  #[vkArr 0 1, vkArr 0 2, vkArr 1 1, vkArr 1 2, vkArr 2 1, vkArr 2 2]

@[expose] def wordA : List ℕ := [1, 5, 0, 3, 2, 5, 3, 1, 4, 1, 2, 5, 1, 3, 1, 0, 5, 1, 2, 0, 4]

@[expose] def wordB : List ℕ := [0, 3, 4, 0, 3, 5, 1, 3, 5, 2, 0, 2]

@[expose] def evalWord (w : List ℕ) : Array ℕ :=
  w.foldl (fun t i => compA 315 t vGens[i]!) (idA 315)

@[expose] def inKlein (g h t : Array ℕ) : Bool :=
  eqA 315 t (idA 315) || eqA 315 t g || eqA 315 t h || eqA 315 t (compA 315 g h)

@[expose] def chkE : Bool :=
  okA xArr && okA zArr && eqA 315 (compA 315 xArr (compA 315 xArr xArr)) (idA 315) &&
    eqA 315 (compA 315 zArr (compA 315 zArr zArr)) (idA 315) && commA xArr zArr &&
    !(eqA 315 xArr (idA 315)) && !(eqA 315 zArr (idA 315)) && !(eqA 315 zArr xArr) &&
    !(eqA 315 zArr (compA 315 xArr xArr))

@[expose] def chkV : Bool :=
  (List.range 6).all (fun i =>
    okA vGens[i]! && eqA 315 (compA 315 vGens[i]! vGens[i]!) (idA 315)) &&
    (List.range 3).all fun k =>
      commA vGens[2 * k]! vGens[2 * k + 1]! &&
        [xArr, zArr].all fun e =>
          inKlein vGens[2 * k]! vGens[2 * k + 1]! (conjA 315 e vGens[2 * k]!) &&
            inKlein vGens[2 * k]! vGens[2 * k + 1]! (conjA 315 e vGens[2 * k + 1]!)

@[expose] def chkGen : Bool :=
  eqA 315 (evalWord wordA) autStrong[0]! && eqA 315 (evalWord wordB) autStrong[1]!

@[expose] def j2GenCheck : Bool := chkE && chkV && chkGen

end CFSG.RankThree.PartTwo.Sec17.PropU.J2Gen
