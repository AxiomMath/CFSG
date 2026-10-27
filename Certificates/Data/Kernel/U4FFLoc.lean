module

public import CFSG.HardMathSupport.U4FF.ClassLocBase
public import CFSG.Assembly.QuasithinDefs
public import CFSG.GroupTheory.LocalCores.Fitting
public import CFSG.LieType.BorelTits.CompleteFlag
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBDerivedNormalSectionBound
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHeldSmallCorePrimeCore
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalDescentEndpoint
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalFiveStructure
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalFixedTransfer
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointActionModels
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointPlusBorelModel
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalScalarSquareField
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalScalarSquareStructure
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSixComponentsCover
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSixModelGeometry
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalTraceZeroCoordinates
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBProjectiveInvolutionStructure
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBSymplecticBField
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBSymplecticBLinear
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBSymplecticRepresentationOdd
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProper
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProperGroups
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpExclusion
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasFive
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasSix
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalReflectionSplitting
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalStandardFormsRegular
public import CFSG.LocalAnalysis.SectionRank.PRank
public import CFSG.LocalAnalysis.SectionRank.SQT
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Defs
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.FiniteFieldFixedSubfieldCard
public import TauCeti.LinearAlgebra.Dimension.IsQuadraticExtension
public import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalBasis
public import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalGroup.LowRank

public section

namespace CFSG.KC.U4FFLoc

open CFSG.HardMathSupport.U4FF

@[expose] def applyL : List ℕ → ℕ → ℕ
  | [], _ => 0
  | a :: A, v => (if v % 2 = 1 then a else 0) ^^^ applyL A (v / 2)

@[expose] def mulL (A B : List ℕ) : List ℕ := B.map (applyL A)

@[expose] def addL (A B : List ℕ) : List ℕ := List.zipWith (fun a b => a ^^^ b) A B

@[expose] def oneL (m : ℕ) : List ℕ := (List.range m).map fun j => 1 <<< j

@[expose] def zeroL (m : ℕ) : List ℕ := List.replicate m 0

@[expose] def zrowL (n zeta : ℕ) : List ℕ :=
  (List.range n).map fun x => if zeta.testBit x then 1 else 0

@[expose] def dimL (fs : List FK) : ℕ := (fs.map FK.dim).prod

@[expose] def derN (K : FK) (i j : Fin 4) (a b : ℕ) : ZMod 2 :=
  if h : a < K.dim ∧ b < K.dim then derK K i j ⟨a, h.1⟩ ⟨b, h.2⟩ else 0

@[expose] def derL (K : FK) (i j : Fin 4) : List ℕ :=
  (List.range K.dim).map fun b =>
    (List.range K.dim).foldl (fun acc a => if derN K i j a b = 1 then acc ||| (1 <<< a) else acc) 0

@[expose] def kronCol (d ca : ℕ) : ℕ → ℕ → ℕ
  | 0, _ => 0
  | n + 1, cb => (if cb % 2 = 1 then ca else 0) ^^^ (kronCol d ca n (cb / 2) <<< d)

@[expose] def kronStep (d n : ℕ) (der : List ℕ) (r : ℕ) (P Q : List ℕ) : List ℕ :=
  (List.range (d * n)).map fun y =>
    kronCol d (1 <<< (y % d)) n (P.getD (y / d) 0) ^^^
      (if r = 0 then 0 else kronCol d (der.getD (y % d) 0) n (Q.getD (y / d) 0))

@[expose] def tabDK : List FK → Fin 4 → Fin 4 → ℕ → List ℕ
  | [], _, _, r => [if r = 0 then 1 else 0]
  | K :: fs, i, j, r =>
    kronStep K.dim (dimL fs) (derL K i j) r (tabDK fs i j r) (tabDK fs i j (r - 1))

end CFSG.KC.U4FFLoc
