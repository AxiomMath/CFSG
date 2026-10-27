module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1677ThreeMain
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC165Main
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenTI
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.PartOne
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section18.OmegaSixMinusK
public import CFSG.GH74.GLS.Stage2.Bender.Thm2.Der10Two
public import CFSG.GroupTheory.SupCommute
public import CFSG.HardMathSupport.Foote.E27.TableMat
public import CFSG.LargeExtraspecial.S6Seven
public import CFSG.LargeExtraspecial.S6SixB
public import CFSG.LargeExtraspecial.S6SixC
public import CFSG.LargeExtraspecial.S6ThreeD
public import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoConfig
public import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoEscape
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.CenterHopf
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVIbDefs
public import CFSG.LocalAnalysis.AGLEmbedding.ZZPrimeDefs
public import CFSG.LocalAnalysis.ComponentClassification.SolAltLitBasic
public import CFSG.LocalAnalysis.RankThreeUC.AGL81U4FFDefs
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenThreeB2s
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenThreeSemiBotIrr
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.R1613gGapM
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1KitDefs
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC34UniqueP
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightD5Abstract
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightS1Fam
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightS1OmegaComp
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightS1Two
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154PStar
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven2TwentyEndOmega
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven2TwentyOddOMinus
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven2TwentyTwoCapAltNorm
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven3Close16CoverR119
public import CFSG.LocalAnalysis.UniquenessCase.UC22P21a
public import CFSG.LocalAnalysis.UniquenessCase.UC22P2214e2
public import CFSG.Quasithin.Background.G10Local
public import CFSG.Quasithin.EmptyFaithful.S153ZN
public import CFSG.Quasithin.EmptyFaithful.S153ZO
public import CFSG.Quasithin.EmptyFaithful.S153ZP
public import CFSG.Quasithin.Vol2.GoldschmidtF431UnPre
public import CFSG.RankThree.PartTwo.Sec15.Item1514Steps1515S17
public import CFSG.RankThree.PartTwo.Sec15.Item1514StepsQuot
public import CFSG.RankThree.PartTwo.Sec15.Item1514StepsS17
public import CFSG.RankThree.PartTwo.Sec15.Item158Res2ProofInner
public import CFSG.RankThree.PartTwo.Sec17.Item175Proof
public import CFSG.RankThree.PartTwo.Sec17.Item17ParaHJ
public import CFSG.Sporadic.Schreier.J4SCommGenBase1
public import Certificates.Data.E27Q2O

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)

variable {G : Type} [Group G] [Finite G]

@[expose] def R9_24X (D : Data G) : Prop :=
  ∀ (L P X : Subgroup G) (n : ℕ), L ∈ calC D.M → D.M ≤ normalizer (L : Set G) → 1 < n →
    IsU4 (Bar2 L) n → ParabolicOf L P → X = F07.DerInf P → IsL2 (Bar2 X) (2 * n) →
    pCoreOf 2 X ≠ ⊥ → (∀ A ∈ F09.Inv9' D.M X 3, ⁅A, X⁆ ≤ pCoreOf 2 A) →
    IsStronglyPEmbedded 3 D.M → UniqueMax D.M X

structure S16c6Coords (V₀ V L : Subgroup G) (hV : IsElemAbelian 2 V) where
  F : Type
  [field : Field F]
  [fin : Finite F]
  b : F
  c : F
  card_eq : Nat.card F = 2 ^ 3
  irr : ∀ s : F, s ^ 2 + b * s + c ≠ 0
  ε : ↥(lBar V₀ V hV L) ≃* ↥(StatedOmega (StatedQuadMinus 3 F b c))
  ψ : ↥(⊤ : Subgroup (Vtil V₀ V hV)) ≃*
    Multiplicative (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2 → F)
  coords : S18.NatCoordsOmegaMinusOn (lBar V₀ V hV L) ⊤ (fun _ _ s _ => Subgroup.mem_top s)
    F b c ε ψ

attribute [instance] S16c6Coords.field S16c6Coords.fin

namespace S16c6Coords

variable {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}

@[expose] noncomputable def vec (c : S16c6Coords V₀ V L hV) (w : G) (hw : w ∈ V) :
    Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2 → c.F :=
  Multiplicative.toAdd (c.ψ ⟨mkTil V₀ V hV (IntMod.mk hV ⟨w, hw⟩), Subgroup.mem_top _⟩)

@[expose] def Singular (c : S16c6Coords V₀ V L hV) (w : G) (hw : w ∈ V) : Prop :=
  mkTil V₀ V hV (IntMod.mk hV ⟨w, hw⟩) ≠ 1 ∧ StatedQuadMinus 3 c.F c.b c.c (c.vec w hw) = 0

@[expose] def NonSingular (c : S16c6Coords V₀ V L hV) (w : G) (hw : w ∈ V) : Prop :=
  StatedQuadMinus 3 c.F c.b c.c (c.vec w hw) ≠ 0

end S16c6Coords

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
