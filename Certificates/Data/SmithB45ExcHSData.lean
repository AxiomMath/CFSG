module

public import CFSG.Quasithin.Background.SmithB45ExcHSRuWit
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L246B42HSCheckInputs
public import CFSG.Foundations
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L246B42HSData
public import CFSG.LocalAnalysis.SectionRank.SQT

public section

namespace CFSG.Quasithin.B45Exc.HS

open CFSG.Quasithin.B45Exc.Tab CFSG.QuasithinUnique.Setup.X1 CFSG.QuasithinUnique.Bridge.HSExcl
  CFSG.Monster.B.Co2.Native

@[expose] def hsGens : List PArr := [hsA0P, hsA1P]

@[expose] def hsInvProd (t : PArr) (w : List ℤ) : PArr :=
  pMul 3850 t (pConj 3850 (pWord 3850 hsGens w) t)

structure DimWit where
  d : ℕ
  c : ℕ
  e : ℕ
  e' : ℕ
  g : List ℤ

@[expose] def hsW0 : List ℤ :=
  [-2, 1, -2, -1, -1, 2, 2, 1, -2, -1]

@[expose] def hsW1g : List ℤ :=
  [1, -2, -1, 2, -1, 2, 2, 1]

@[expose] def hsW1x : List ℤ :=
  [-2, -1, 2, -1, -2, -2, -1, -2, -2, -1, 2, -1, -2, -1, 2, -1, 2, -1, 2, 2, -1, 2, 2, -1, -2,
   -1, 2, -1, 2, -1, 2, 2, -1, -2, -1, 2, -1, -2, -1, -2]

@[expose] def hsW1y : List ℤ :=
  [1, -2, -2, 1, 2, 2, 2, 1, -2, -2, 1, -2, -2, 1, -2, -1, 2, 2, -1, 2, 2, -1, 2, -1, -2, -1, 2,
   2, 2, 1, 2, 1, 2, 2, 1, 2, 2, 1, 2]

@[expose] def hsW3g : List ℤ :=
  [-1, 1, -2, 1, -1, -1, 2, 2]

@[expose] def hsW3x : List ℤ :=
  [-2, -1, 2, -1, 2, -1, 2, -1, 2, 2, 2, 1, -2, 1, -2, -2, 1, 2, -1, -2, -2, -1, 2, -1, 2, -1,
   2, 2, -1, 2, -1, 2, -1]

@[expose] def hsW3y : List ℤ :=
  [1, -2, -2, 1, 2, 2, 2, 1, 2, 1, -2, -2, 1, 2, 2, 1, -2, 1, 2, 2, -1, 2, 1, 2, 2, 1, 2, 1, 2,
   2, 1, 2, 2, 1, 2, 2]

@[expose] def hsGenWits : List GenWit := [
  { basis := [2, 17, 20, 75],
    g :=
      [2, 1, -2, 1, -2, 2, 2, -2, 2, -1],
    ws := [
      [-1, -2],
      [-1, -2, -3, -5, -6, -2, -3, -5, -2, -3, -6, -1, 6, 4, 3, 6, 1, -8, -4]] },
  { basis := [2, 17, 22, 79],
    g :=
      [2, 2, -2, -1, 2, -1, -1, -1, -2, 2, -1],
    ws := [
      [-2, -1],
      [7, 1, -2, 6, 5, 4, 1, 7, 4, 7, 4, 8, 4, 3, 5, 2, 5]] },
  { basis := [2, 17, 56, 78],
    g :=
      [-2, 1, -2, 1, 1, 1, -2, -1],
    ws := [
      [-2, -1],
      [-4, -8, -3, 6, 5, 4, 8, 2, -1, -6, -1, -6, -3, -8, 1, -3]] },
  { basis := [6, 10, 20, 29],
    g :=
      [2, 2, -2, 2, 2, 1, -2, -1, 1],
    ws := [
      [-1, -2, -4],
      [5, -1, -2, -7, -4, -7, -2, 1, -2, -3, -5, -4, -8, -3, 2, -1, -5, -4, -6, -1, -5, 4, 6, 3,
       5]] },
  { basis := [6, 15, 27, 32],
    g :=
      [2, 2, -1, 1, 1, -2, 2, 2],
    ws := [
      [-1, -2, -4],
      [-3, -6, -3, -4, -8, -3, -6, -3, -1, 7, 4, 2, 1, 7, 1, -3]] },
  { basis := [9, 13, 14, 22],
    g :=
      [-1, 2, -2, -2, -2, 2, -2, -1],
    ws := [
      [-1, -3],
      [-4, -6, -2, -3, -6, 2, 6, -5, -1, -8, -3, -5, 6, 8, 1]] },
  { basis := [9, 14, 25, 55],
    g :=
      [2, 1, 2, 2, 1, 1, 2, -2],
    ws := [
      [-1, -2],
      [8, 6, 3, 5, -8, -2, -6, -8, -6, -2, -8, -7, -2, -6, -4, -7, -3, -1, -2]] },
  { basis := [1, 2, 6, 17, 52],
    g :=
      [-2, 2, 2, -1, -2, -1, -2, -1, -1],
    ws := [
      [-2, -4],
      [-5, -8, -1, -9, -2, -10, -2, -4, -7, -9, -3, -3, -4, -5, -8]] },
  { basis := [1, 2, 9, 14, 53],
    g :=
      [2, 2, -1, -2],
    ws := [
      [-1, -5, -8, -2, -8, -2],
      [-3, -7, -2, -4, -7, 3, 7, 8, 2, 7, 4, -1, -7, -10, -1, -8]] },
  { basis := [2, 6, 17, 20, 75],
    g :=
      [-2, -1, -2, 1, -1, 2, 1, 1, -2, 2, 2, 2],
    ws := [
      [-1, -3],
      [10, 4, 2, -1, 10, 1, 8, 3, 1, -2, -8, -4, -6, -10]] },
  { basis := [2, 6, 17, 22, 38],
    g :=
      [2, -1, 1, 1, 2, -2, 2],
    ws := [
      [-2, -1, -2, -3],
      [4, 9, 3, 2, 1, -2, -5, -9, 6, 5, 6, 4, 7, 2]] },
  { basis := [2, 6, 17, 26, 38],
    g :=
      [1, 2, -2, 1, 1, -2, -1, -1, 1, -2, 2],
    ws := [
      [-1, -3],
      [-6, 2, 10, 9, 8, 1, 8, 3, 6, 5, 4, -2]] },
  { basis := [2, 9, 14, 20, 53],
    g :=
      [1, -1, 1, 2, -2, -1, -2, 2, 1, 1, -2, -1],
    ws := [
      [-3, -2],
      [8, 7, -2, -8, 9, 3, 9, 7, 3, -5, -7, -4, -6]] },
  { basis := [2, 9, 14, 22, 79],
    g :=
      [2, -2, 2, -1, 2, -1, 1, 1, 1, 1],
    ws := [
      [-3, -2],
      [2, 7, 2, -6, 2, 6, 3, 7, 2, 7, -1, -7, -2, -8, -1, 6, 7]] },
  { basis := [2, 9, 14, 26, 63],
    g :=
      [-1, 1, 1, -1, -1, -1, -1, 2, 2],
    ws := [
      [-2, -3],
      [1, -9, -1, -9, -1, 8, -2, -8, -5, -7, -8, 2, 8, -4, -10, -4, -7]] }]

@[expose] def hsDimWits : List DimWit := [
  { d := 59, c := 6, e := 28, e' := 30,
    g :=
      [-2, -1, 2, -1, 2, -1, -2, -1, 2, 2, -1, -2, -2, -2, 1, 2, 1, 2, 1, 2, 2, 1, 2, 1, 2, 1,
       2, -1, -2, -2, -1, -2, -2, -1, -2, -1, -2, -2, -1] },
  { d := 39, c := 9, e := 1, e' := 53,
    g :=
      [2, 2, 1, -2, 1, -2, 1, -2, -2, 1, -2, 1, 2, 1, -2, -2, 1, -2, 1, -2, 1, -2, 1, 2, 1, 2,
       2, 1, -2, -2, 1, 2, 2, 1, 2, 1, 2] },
  { d := 59, c := 6, e := 2, e' := 17,
    g :=
      [-1, -2, -1, 2, 2, 1, -2, -2, 1, -2, -2, 1, 2, 1, -2, 1, 2, 2, 2, 1, -2, -2, 1, -2, 1, -2,
       -2, -1, 2, 2, -1, 2, -1, 2, -1, 2, -1, -2, -2, -2, -2, -1, 2, 2, -1, -2, -2, -1, 2, 2] },
  { d := 59, c := 6, e := 2, e' := 17,
    g :=
      [1, -2, -1, -2, -2, -1, -2, -1, -2, -2, -1, 2, -1, -2, -2, -1, -2, -2, -1, -2, -2, -1, -2,
       -1, -2, 1, -2, 1, -2, -2, 1, 2, 2] },
  { d := 58, c := 6, e := 2, e' := 17,
    g :=
      [1, -2, -2, 1, 2, 2, 1, -2, -2, 1, 2, 2, 2, 2, 1, 2, 2, 1, -2, -2, 1, 2, 2, 1, -2, -2, 1,
       2, 1, -2, 1, -2, 1, 2, 1, -2, -2, 1, 2, 1, -2] },
  { d := 39, c := 9, e := 2, e' := 17,
    g :=
      [2, 2, 1, -2, -2, 1, -2, 1, 2, 1, 2, 2, 1, -2, 1, 2, 2, 1, -2, -2, 1, -2, 1, -2, 1, 2, -1,
       -2, -2, -2, -2, -1, 2, 2, -1] },
  { d := 39, c := 9, e := 2, e' := 17,
    g :=
      [-2, -2, 1, 2, 2, 1, 2, 1, 2, 1, -2, 1, 2, 1, 2, 2, 1, 2, 1, 2, 1, 2, 2, 1, -2, -2, 1, -2,
       -2, 1, 2, 2, -1, -2, -2, -1, 2, 2, -1, -2, -1, -2, -2] },
  { d := 39, c := 9, e := 17, e' := 2,
    g :=
      [-2, -2, 1, 2, 2, 1, -2, -2, 1, 2, 2, 2, 1, 2, 2, 1, 2, 2, 1, -2, 1, 2, 1, -2, -1, -2, -1,
       2, -1, -2, -1, 2, 2, -1, 2, -1, -2, 1, -2, 1, 2, 1, -2, 1, 2, 2, 1, 2, 1] }]

@[expose] def hsClassCheck0 : Bool := orderCheck 3850 5 (hsInvProd (hsTP 5) hsW0)

@[expose] def hsClassCheck1 : Bool :=
  cfgCheck 3850 5 (hsInvProd (hsTP 12) hsW1g) (pWord 3850 hsGens hsW1x) (pWord 3850 hsGens hsW1y)

@[expose] def hsClassCheck3 : Bool :=
  cfgCheck 3850 5 (hsInvProd (hsTP 34) hsW3g) (pWord 3850 hsGens hsW3x) (pWord 3850 hsGens hsW3y)

@[expose] def hsFixCheck : Bool :=
  fixCountA 3850 (hsTA 5) == 170 && fixCountA 3850 (hsTA 12) == 30 &&
    fixCountA 3850 (hsTA 21) == 350 && fixCountA 3850 (hsTA 34) == 46

@[expose] def hsSylAl : Array (Array ℕ) :=
  sylBuild 3850 1024 hsSylGens (parseNats hsSylParStr) (parseNats hsSylLabStr)

@[expose] def hsUInv : Array (Array ℕ) :=
  ((sylInv 3850 1024 hsSylAl).map fun i => hsSylAl[i]!).toArray

@[expose] def hsUTab : InvTab 3850 := InvTab.build 3850 hsUInv [0, 5]

@[expose] def hsUFix : Array ℕ := hsUInv.map (fixCountA 3850)

@[expose] def dimWitOK (w : DimWit) : Bool :=
  let G := pWord 3850 hsGens w.g
  let xc : PArr := (hsUTab.elt w.c, hsUTab.elt w.c)
  decide (w.d < hsUTab.m) && decide (w.c < hsUTab.m) && decide (w.e < hsUTab.m) &&
    decide (w.e' < hsUTab.m) && hsUFix[w.d]! == 46 && hsUFix[w.c]! == 350 &&
    (hsUFix[w.e]! == 170 || hsUFix[w.e]! == 30) &&
    (hsUFix[w.e']! == 170 || hsUFix[w.e']! == 30) &&
    eqA 3850 (pMul 3850 G xc).1 (pMul 3850 xc G).1 &&
    orderCheck 3850 5
      (pMul 3850 (pConj 3850 G (hsUTab.elt w.e, hsUTab.elt w.e)) (hsUTab.elt w.e', hsUTab.elt w.e'))

@[expose] def hsPred4 (l : List ℕ) : Bool :=
  let S := hsUTab.subprodsI l
  (S.any fun s => decide (s < hsUTab.m) && (hsUFix[s]! == 30 || hsUFix[s]! == 46)) ||
    hsGenWits.any fun w => w.basis.all S.contains

@[expose] def hsPred5 (l : List ℕ) : Bool :=
  let S := hsUTab.subprodsI l
  (hsGenWits.any fun w => w.basis.all S.contains) &&
    hsDimWits.any fun w => [w.d, w.c, w.e, w.e'].all S.contains

end CFSG.Quasithin.B45Exc.HS
