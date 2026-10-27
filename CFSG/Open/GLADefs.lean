module

public import Mathlib
public import CFSG.Assembly.GL83LieDefs
public import CFSG.Assembly.GL83HalfSplitSection16
public import CFSG.Open.Defs
public import CFSG.Open.GeneratedCore
import CFSG.Assembly.GL83LocalCore

public section

namespace CFSG.Open
open scoped MatrixGroups

noncomputable section

abbrev GLALieTag := @CFSG.Assembly.LargeEvenLieTag

abbrev GLALabel := @CFSG.Assembly.LargeEvenLabel

abbrev GLAInLambda2 := @CFSG.Assembly.LargeEvenInLambda2

abbrev GLAUntwisted := @CFSG.Assembly.LargeEvenUntwisted

abbrev GLASplit := @CFSG.Assembly.LargeEvenSplit

abbrev GLAHalfSplit := @CFSG.Assembly.LargeEvenHalfSplit

abbrev GLASplit16 := @CFSG.Assembly.LargeEvenSplit16

abbrev GLAHalfSplit16 := @CFSG.Assembly.LargeEvenHalfSplit16

abbrev GLAHalfSplitWithE6Four := @CFSG.Assembly.LargeEvenHalfSplitWithE6Four

abbrev GLAGraphAut := @CFSG.Assembly.LargeEvenGraphAut

abbrev GLAInnSet := @CFSG.Assembly.LargeEvenInnSet

abbrev GLAScalars := @CFSG.Assembly.LargeEvenScalars

abbrev GLAProj := @CFSG.Assembly.LargeEvenProj

abbrev GLAProjMk := @CFSG.Assembly.LargeEvenProjMk

abbrev GLASLGroup := @CFSG.Assembly.LargeEvenSLGroup

abbrev GLASUGroup := @CFSG.Assembly.LargeEvenSUGroup

abbrev GLASpForm := @CFSG.Assembly.LargeEvenSpForm

abbrev GLASpGroup := @CFSG.Assembly.LargeEvenSpGroup

abbrev GLAOrthGroup := @CFSG.Assembly.LargeEvenOrthGroup

abbrev GLAOmega := @CFSG.Assembly.LargeEvenOmega

abbrev GLAQPlus := @CFSG.Assembly.LargeEvenQPlus

abbrev GLAMinusIdx := @CFSG.Assembly.LargeEvenMinusIdx

abbrev GLAQMinus := @CFSG.Assembly.LargeEvenQMinus

abbrev GLAGUSet := @CFSG.Assembly.LargeEvenGUSet

abbrev GLAGSpSet := @CFSG.Assembly.LargeEvenGSpSet

abbrev GLAMatConjImage := @CFSG.Assembly.LargeEvenMatConjImage

abbrev GLAMatFieldImage := @CFSG.Assembly.LargeEvenMatFieldImage

abbrev GLAFrobBlock := @CFSG.Assembly.LargeEvenFrobBlock

abbrev GLAPhiQ := @CFSG.Assembly.LargeEvenPhiQ

abbrev GLARawCont := @CFSG.Assembly.LargeEvenRawCont

abbrev GLARecipeLinear := @CFSG.Assembly.LargeEvenRecipeLinear

abbrev GLARecipeUnitary := @CFSG.Assembly.LargeEvenRecipeUnitary

abbrev GLARecipeSymplectic := @CFSG.Assembly.LargeEvenRecipeSymplectic

abbrev GLARecipeOmegaPlus := @CFSG.Assembly.LargeEvenRecipeOmegaPlus

abbrev GLARecipeOmegaMinus := @CFSG.Assembly.LargeEvenRecipeOmegaMinus

abbrev GLACartanG2 := @CFSG.Assembly.LargeEvenCartanG2

abbrev GLACartanF4 := @CFSG.Assembly.LargeEvenCartanF4

abbrev GLACartanD4 := @CFSG.Assembly.LargeEvenCartanD4

abbrev GLACartanE := @CFSG.Assembly.LargeEvenCartanE

abbrev GLARhoE6 := @CFSG.Assembly.LargeEvenRhoE6

abbrev GLARhoD4 := @CFSG.Assembly.LargeEvenRhoD4

abbrev GLARhoF4 := @CFSG.Assembly.LargeEvenRhoF4

abbrev GLAReflect := @CFSG.Assembly.LargeEvenReflect

abbrev GLAIsRoot := @CFSG.Assembly.LargeEvenIsRoot

abbrev GLARootIndex := @CFSG.Assembly.LargeEvenRootIndex

abbrev GLAChevModule := @CFSG.Assembly.LargeEvenChevModule

abbrev GLAChevGL := @CFSG.Assembly.LargeEvenChevGL

abbrev GLAHVec := @CFSG.Assembly.LargeEvenHVec

abbrev GLARootVec := @CFSG.Assembly.LargeEvenRootVec

abbrev GLAStringUp := @CFSG.Assembly.LargeEvenStringUp

abbrev GLAStringDown := @CFSG.Assembly.LargeEvenStringDown

abbrev GLAXOp := @CFSG.Assembly.LargeEvenXOp

abbrev GLAYOp := @CFSG.Assembly.LargeEvenYOp

abbrev GLAChevGroup := @CFSG.Assembly.LargeEvenChevGroup

abbrev GLAEntrywise := @CFSG.Assembly.LargeEvenEntrywise

abbrev GLADiagramMap := @CFSG.Assembly.LargeEvenDiagramMap

abbrev GLADiagMap := @CFSG.Assembly.LargeEvenDiagMap

abbrev GLACenterQuot := @CFSG.Assembly.LargeEvenCenterQuot

abbrev GLACenterMk := @CFSG.Assembly.LargeEvenCenterMk

abbrev GLAChevDiagImage := @CFSG.Assembly.LargeEvenChevDiagImage

abbrev GLAChevIDImage := @CFSG.Assembly.LargeEvenChevIDImage

abbrev GLAParentConjImage := @CFSG.Assembly.LargeEvenParentConjImage

abbrev GLAChevParentIDImage := @CFSG.Assembly.LargeEvenChevParentIDImage

abbrev GLAChevFieldImage := @CFSG.Assembly.LargeEvenChevFieldImage

abbrev GLAChevH := @CFSG.Assembly.LargeEvenChevH

abbrev GLATwistedH := @CFSG.Assembly.LargeEvenTwistedH

abbrev GLATwF4Exp := @CFSG.Assembly.LargeEvenTwF4Exp

abbrev GLATwF4H := @CFSG.Assembly.LargeEvenTwF4H

abbrev GLASzGens := @CFSG.Assembly.LargeEvenSzGens

abbrev GLASzGroup := @CFSG.Assembly.LargeEvenSzGroup

abbrev GLARecipeChevalley := @CFSG.Assembly.LargeEvenRecipeChevalley

abbrev GLARecipeTwisted := @CFSG.Assembly.LargeEvenRecipeTwisted

abbrev GLARecipeSuzuki := @CFSG.Assembly.LargeEvenRecipeSuzuki

abbrev GLARecipeTwF4 := @CFSG.Assembly.LargeEvenRecipeTwF4

abbrev GLARawDatum := @CFSG.Assembly.LargeEvenRawDatum

abbrev GLAMarkProp := @CFSG.Assembly.LargeEvenMarkProp

abbrev GLAMarking := @CFSG.Assembly.LargeEvenMarking

abbrev GLAInduces := @CFSG.Assembly.LargeEvenInduces

abbrev GLAPrimeField := @CFSG.Assembly.LargeEvenPrimeField

abbrev GLAIsU42 := @CFSG.Assembly.LargeEvenIsU42


section Local

variable {G : Type*} [Group G]

@[expose] noncomputable def GLATwoLocalRank (p : ℕ) (G : Type*) [Group G] [Finite G] : ℕ :=
  gl83_local% CFSG.Assembly.GL83Local.twoLocalRank p G

@[expose] def GLABeta (k : ℕ) (G : Type*) [Group G] [Finite G] : Set ℕ :=
  gl83_local% CFSG.Assembly.GL83Local.beta GLATwoLocalRank k G

@[expose] def GLAIsBmax [Finite G] (p : ℕ) (B : Subgroup G) : Prop :=
  gl83_local% CFSG.Assembly.GL83Local.isBmax GLATwoLocalRank p B

@[expose] def GLAPPrimeCore (p : ℕ) (H : Type*) [Group H] : Subgroup H :=
  CFSG.pPrimeCore p H

instance GLAPPrimeCore.normal (p : ℕ) (H : Type*) [Group H] : (GLAPPrimeCore p H).Normal :=
  Subgroup.sSup_normal _ fun _ hN => hN.1

@[expose] def GLAPPrimeCoreOf (p : ℕ) (H : Subgroup G) : Subgroup G :=
  gl83_local% CFSG.Assembly.GL83Local.pPrimeCoreOf GLAPPrimeCore p H

@[expose] noncomputable def GLAWeakCore [Finite G] (p : ℕ) (P : Subgroup G) : Subgroup G :=
  gl83_local% CFSG.Assembly.GL83Local.weakCore p P

@[expose] def GLAWeakCoreLocal (G : Type*) [Group G] [Finite G] (p : ℕ) : Prop :=
  gl83_local% CFSG.Assembly.GL83Local.weakCoreLocal G GLAWeakCore p

@[expose] def GLADelta (p : ℕ) (D : Subgroup G) : Subgroup G :=
  ⨅ (d : G) (_ : d ∈ D) (_ : d ≠ 1), GLAPPrimeCoreOf p (Subgroup.centralizer ({d} : Set G))

@[expose] def GLADeltaZero (G : Type*) [Group G] [Finite G] (p : ℕ) : Prop :=
  ∀ B : Subgroup G, GLAIsBmax p B → ∀ D : Subgroup G, D ≤ B → IsElemAbelian p D →
    Nat.card D = p ^ 2 →
      (5 ≤ p → Odd (Nat.card (GLADelta p D))) ∧
        (p = 3 → Odd (Nat.card (⁅GLADelta p D, B⁆ : Subgroup G)))

@[expose] def GLAIsMaxTwoLocal (M : Subgroup G) : Prop :=
  gl83_local% CFSG.Assembly.GL83Local.isMaxTwoLocal M

abbrev GLASymplecticType := @CFSG.Assembly.LargeEvenSymplecticType

@[expose] def GLAGF2Type (G : Type*) [Group G] [Finite G] : Prop :=
  gl83_local% CFSG.Assembly.GL83Local.gf2Type G GLAIsMaxTwoLocal @GLASymplecticType @GLAIsBmax

@[expose] def GLALayer (H : Subgroup G) : Subgroup G :=
  gl83_local% CFSG.Assembly.GL83Local.layer @IsComponentOf H

@[expose] def GLAPComponent (p : ℕ) (X L : Subgroup G) : Prop :=
  gl83_local% CFSG.Assembly.GL83Local.pComponent @IsComponentOf @IsSubnormal GLAPPrimeCore p X L

@[expose] def GLAPLayer (p : ℕ) (X : Subgroup G) : Subgroup G :=
  gl83_local% CFSG.Assembly.GL83Local.pLayer GLAPComponent p X

@[expose] def GLASStar [Finite G] (p : ℕ) (B : Subgroup G) (x : G) (L : Subgroup G) : Prop :=
  gl83_local% CFSG.Assembly.GL83Local.sStar @IsComponentOf @GLAIsBmax p B x L

@[expose] def GLASHat [Finite G] (p : ℕ) (B : Subgroup G) (x : G) (L : Subgroup G) : Prop :=
  gl83_local% CFSG.Assembly.GL83Local.sHat @GLAIsBmax GLAPComponent GLAPPrimeCoreOf p B x L

@[expose] def GLAStdSubPre (p : ℕ) (B : Subgroup G) (x : G) (L D K : Subgroup G) : Prop :=
  gl83_local% CFSG.Assembly.GL83Local.stdSubPre @IsComponentOf GLALayer p B x L D K

abbrev GLASmall := @CFSG.Assembly.LargeEvenSmall

@[expose] def GLAStdSub (p : ℕ) (B : Subgroup G) (x : G) (L D K : Subgroup G) : Prop :=
  gl83_local% CFSG.Assembly.GL83Local.stdSub GLAStdSubPre GLASmall p B x L D K

@[expose] def GLANeighbor (p : ℕ) (x y : G) (J D K : Subgroup G) : Prop :=
  gl83_local% CFSG.Assembly.GL83Local.neighbor GLAPLayer GLAPPrimeCoreOf p x y J D K

@[expose] def GLAIsNeighborOf [Finite G] (p : ℕ) (B : Subgroup G) (x : G) (L : Subgroup G) (y : G)
    (J : Subgroup G) : Prop :=
  gl83_local% CFSG.Assembly.GL83Local.isNeighborOf (GLASHat p B) (GLAStdSub p B x L)
      (GLANeighbor p x) y J

@[expose] def GLAStandardType [Finite G] (p : ℕ) (B : Subgroup G) (x : G) (L : Subgroup G) : Prop :=
  CFSG.Assembly.LargeEvenStandardTypeOf p B x L (GLAIsNeighborOf p B x L) (GLAStdSub p B x L)
    (GLASHat p B) (GLANeighbor p x) (GLAPPrimeCoreOf p)

end Local

end

end CFSG.Open
