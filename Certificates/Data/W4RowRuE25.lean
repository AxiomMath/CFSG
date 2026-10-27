module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L246B42RuCheckInputs
public import CFSG.Quasithin.Background.SmithB45ExcHSRuWit
public import CFSG.Foundations
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L246B42RuData
public import CFSG.LocalAnalysis.SectionRank.SQT
public import CFSG.Sporadic.Schreier.RuEnum

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Row

open CFSG.QuasithinUnique.Setup.X1 CFSG.QuasithinUnique.Bridge.RuExcl CFSG.Sporadic.RuSchreier
  CFSG.Monster.B.Co2.Native CFSG.Quasithin.B45Exc.Tab

@[expose] def invPackCheck (n p m : ℕ) (τ y w h : PArr) (cs : List (ℕ × ℕ)) : Bool :=
  let e := idA n
  let pr := fun ab : ℕ × ℕ => compA n (powA n y.1 ab.1) (powA n w.1 ab.2)
  eqA n (powA n y.1 p) e && eqA n (powA n w.1 p) e && eqA n (compA n y.1 w.1) (compA n w.1 y.1) &&
    !eqA n y.1 e && allLt p (fun k => !eqA n w.1 (powA n y.1 k)) &&
    eqA n (compA n (compA n τ.1 y.1) τ.2) y.2 && eqA n (compA n (compA n τ.1 w.1) τ.2) w.2 &&
    eqA n (compA n (compA n h.1 y.1) h.2) (pr (cs.getD 0 (0, 0))) &&
    eqA n (compA n (compA n h.1 w.1) h.2) (pr (cs.getD 1 (0, 0))) &&
    eqA n (compA n (compA n h.2 y.1) h.1) (pr (cs.getD 2 (0, 0))) &&
    eqA n (compA n (compA n h.2 w.1) h.1) (pr (cs.getD 3 (0, 0))) &&
    allLt p (fun a => allLt p (fun b => (a == 0 && b == 0) ||
      allLt m (fun k => k == 0 ||
        allLt p (fun j => !eqA n (compA n (compA n (powA n h.1 k) (pr (a, b))) (powA n h.2 k))
          (powA n (pr (a, b)) j)))))

@[expose] def ruE25WYStr : String :=
  "-1 -2 -2 1 2 1 2 1 -2 1 2 1 2 2 1 2 2 1 -2 -1 -1 -1 -1 -1 -2 -1 -2 -2 -1 -2 -2 -1 -2 -2 -1 -2 \
   -2 -1 -1 -1 -1 -1 -2 -1 -2 -1 -2 -2 -2 1 2 1 2 1 2 2 1 2 1 2 2 1 2 1 2 2 -1 -2 -1 -2 -1 2 -1 -2 \
   -1 -2 -1 2 -1 2 -1 -2 -1 -2 -1 -2 -1 -1 -2 -1 2 -1 -2 -2 -1 2 -1 -2 -1 -2 -1 2 1 2 1 2 1 -2 1 2 \
   2 1 -2 1 2 1 2 1 2 1 2 2 1 2 1 2 1 2 2 1 2 2 1 2 1 2 2 1 2 1 2 -1 -2 -1 -2 -2 -1 2 -1 2 -1 2 -1 \
   2 2 1 -2 1 -2 1 -2 1 2 2 1 2 1 2 1 2 1 -2 -2 -2"

@[expose] def ruE25WY : List ℤ := parseInts ruE25WYStr

@[expose] def ruE25WWStr : String :=
  "2 1 2 2 1 -2 1 2 1 -2 1 -2 1 -2 1 -2 -2 -2 -1 -1 -1 -1 -1 -2 -1 -2 -2 -1 -2 -2 -1 -2 -2 -1 -2 \
   -2 -1 -1 -1 -1 -1 -2 -1 -2 -1 -2 -2 -2 1 2 1 2 1 2 2 1 2 1 2 2 1 2 1 2 1 -2 -1 -1 -1 -1 -1 -2 \
   -1 -2 -2 -1 -2 -2 -1 -2 -2 -1 -2 -2 -1 -1 -1 -1 -1 -2 -1 -2 -1 -2 -2 -2 1 2 1 2 1 2 2 1 2 1 2 2 \
   1 2 1 2 1 -2 -2 -2 -1 -1 -1 -1 -1 -2 -1 -2 -2 -1 -2 -2 -1 -2 -2 -1 -2 -2 -1 -1 -1 -1 -1 -2 -1 \
   -2 -1 -2 -2 -2 1 2 1 2 1 2 2 1 2 1 2 2 1 2 1 2 1 -2 -2 -2 -2 -1 -1 -1 -1 -1 -2 -1 -2 -2 -1 -2 \
   -2 -1 -2 -2 -1 -2 -2 -1 -1 -1 -1 -1 -2 -1 -2 -1 -2 -2 -2 1 2 1 2 1 2 2 1 2 1 2 2 1 2 1 2 1 -2 \
   -1 -2 -1 2 -1 2 -1 -2 -1 -2 -1 -2 -2 -1 2 1 -2 1 2 1 2 2 1 -2 1 2 1 2 1 -2 -2 -2 -1 -1 -2 -1 -1 \
   -1 -1 -1 -2 -1 -2 -2 -1 -2 -2 -1 -2 -2 -1 -2 -2 -1 -1 -1 -1 -1 -2 -1 -2 -1 -2 -2 -2 1 2 1 2 1 2 \
   2 1 2 1 2 2 1 2 1 2 1 -2 -2 -2 -2 -1 -1 -1 -1 -1 -2 -1 -2 -2 -1 -2 -2 -1 -2 -2 -1 -2 -2 -1 -1 \
   -1 -1 -1 -2 -1 -2 -1 -2 -2 -2 1 2 1 2 1 2 2 1 2 1 2 2 1 2 1 2 1 -2 -2 -1 -1 -1 -1 -1 -2 -1 -2 \
   -2 -1 -2 -2 -1 -2 -2 -1 -2 -2 -1 -1 -1 -1 -1 -2 -1 -2 -1 -2 -2 -2 1 2 1 2 1 2 2 1 2 1 2 2 1 2 1 \
   2 1 1 2 1 2 2 1 -2 1 -2 1 2 2 1 2 1 2 2 1 2 1 2 2 1 -2 1 2 1 -2 1 -2 -2 1 -2 1 -2 1 -2 1 2 1 2 \
   1 2 1 2 1 2 1 -2 1 -2 1 -2 1 2 1 2 1 2 1 2 1 2 1 -2 1 -2 1 -2 1 2 2 1 2 1 2 1 2 1 -2"

@[expose] def ruE25WW : List ℤ := parseInts ruE25WWStr

@[expose] def ruE25WHStr : String :=
  "-1 -2 -1 2 2 1 2 2 1 2 2 1 2 2 1 -2 1 2 1 -2 -2 -2 -2 -1 -1 -1 -1 -1 -2 -1 -2 -2 -1 -2 -2 -1 -2 \
   -2 -1 -2 -2 -1 -1 -1 -1 -1 -2 -1 -2 -1 -2 -2 -2 1 2 1 2 1 2 2 1 2 1 2 2 1 2 1 2 1 -2 -1 -1 -1 \
   -1 -1 -2 -1 -2 -2 -1 -2 -2 -1 -2 -2 -1 -2 -2 -1 -1 -1 -1 -1 -2 -1 -2 -1 -2 -2 -2 1 2 1 2 1 2 2 \
   1 2 1 2 2 1 2 1 2 1 -2 -1 -1 -1 -1 -1 -2 -1 -2 -2 -1 -2 -2 -1 -2 -2 -1 -2 -2 -1 -1 -1 -1 -1 -2 \
   -1 -2 -1 -2 -2 -2 1 2 1 2 1 2 2 1 2 1 2 2 1 2 1 2 1 2 1 2 1 -2 1 2 1 2 2 1 2 1 2 1 2 1 2 1 -2 1 \
   -2 1 -2 -2 -1 -2 -2 -1 2 -1 2 -1 2 -1 -2 1 -2 1 -2 1 -2 1 2 1 2 1 2 1 2 1 2 1 -2 1 -2 1 -2 1 -2 \
   -1 2 -1 2 -1 2 -1 -2 -2"

@[expose] def ruE25WH : List ℤ := parseInts ruE25WHStr

@[expose] def ruE25Conj : List (ℕ × ℕ) := [(1, 2), (4, 0), (0, 4), (3, 3)]

@[expose] def ruE25Check : Bool :=
  invPackCheck 4060 5 6 ruZtP (pWord 4060 [ruA0P, ruA1P] ruE25WY)
    (pWord 4060 [ruA0P, ruA1P] ruE25WW) (pWord 4060 [ruA0P, ruA1P] ruE25WH) ruE25Conj

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Row
