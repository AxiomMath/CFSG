module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.Defs
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.DefsHyp
public import CFSG.LocalAnalysis.UniquenessCase.UCFront11
public import CFSG.LocalAnalysis.UniquenessCase.UCFront12
public import CFSG.Quasithin.Background.D2Basic
public import CFSG.Foundations.HigherElementaryThompson
public import CFSG.Blueprint.Catalog
public import CFSG.CGT.Timmesfeld75.L2Pair
public import CFSG.CGT.Timmesfeld75.ListWCBasic
public import CFSG.CharacterTheory.CyclicBlocks.Family
public import CFSG.CharacterTheory.Semidihedral.Principal.LargePrimeTorusSylowCentralizers
public import CFSG.CharacterTheory.Semidihedral.Principal.PrimeTorusBlockAlignment
public import CFSG.CharacterTheory.Wreathed.FourPointInvolutionHexagon
public import CFSG.CharacterTheory.Wreathed.OrderThirtyTwoWreathFusion
public import CFSG.ClassicalGroups
public import CFSG.ClassicalInvolution.Models.SymplecticPairs.ShortRoot
public import CFSG.Combinatorics.AperiodicCentralInvolution
public import CFSG.Combinatorics.AperiodicFiveOfSix
public import CFSG.Combinatorics.AperiodicOppositeComponents
public import CFSG.Combinatorics.AperiodicSixteenGraphDistances
public import CFSG.Combinatorics.OuterLayerPredecessors
public import CFSG.GH74.GLS.IVK.L2.F1
public import CFSG.GH74.KGroups.L3EpsNoNormalThree
public import CFSG.GH74.KGroups.L3EpsOutExp
public import CFSG.GH74.KGroups.L3EpsOuterLin
public import CFSG.LieType.SeitzGeneration.NonabHeisThreeCore
public import CFSG.LieType.SeitzGeneration.NonabHeisThreeUnitary
public import CFSG.LieType.SeitzGeneration.UnitaryBlocks
public import CFSG.LieType.SeitzGeneration.UnitaryHyperScope
public import CFSG.LinearAlgebra.LinearGroups.UnitaryThreeOverNine
public import CFSG.LinearAlgebra.LinearGroups.UnitaryThreeOverNineInvolutions
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSixStructure
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogG2EvenCanonicalField
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpExclusion
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpSuzukiCentralizer
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpWedge
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X7bPairs
public import CFSG.LocalAnalysis.SectionRank.QTK.CentreFact.Bounded
public import CFSG.LocalAnalysis.SectionRank.QTK.EvenOrth
public import CFSG.LocalAnalysis.SectionRank.QTK.Exc
public import CFSG.LocalAnalysis.SectionRank.QTK.OddOrth
public import CFSG.LocalAnalysis.UniquenessCase.UC22S20b
public import CFSG.Mathlib.LinearAlgebra.BilinForm.Determinant
public import CFSG.Permutation.UnitaryThreeRecognition.Model
public import CFSG.RankThree.CentralLiftSO.SplitTorusWeyl
public import CFSG.RankThree.OddKernel.CompleteRankComparison
public import CFSG.RankThree.PartOne.KF.ClsPSL
public import CFSG.RankThree.PartOne.KF.SU5Model
public import CFSG.RankThree.PartOne.KF.SymCtxMatrix
public import CFSG.RankThree.PartOne.KF.ToralQuot
public import CFSG.RankThree.PartOne.KF.UnitaryModel
public import CFSG.RankThree.PartOne.S11c.Sec66PSL
public import CFSG.RankThree.PartOne.S11c.Sec66Sp
public import CFSG.RankThree.PartOne.S11c.SuFiveD
public import CFSG.RankThree.PartOne.S11d.OutSymplectic
public import CFSG.RankThree.PartOne.S11d.OutUnitary
public import CFSG.RankThree.PartOne.S9.Sylow.ExclusionBasic
public import CFSG.Sporadic.Schreier.J4SProfileNode
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PSL2NormalizedRootSylowCount

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17

open Subgroup CFSG.Open CFSG.Quasithin
open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.Blueprint (LieModel)
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

@[expose] def Concl17_17 (D : Data G) (V₀ V L : Subgroup G) : Prop :=
  IsJ1 (Bar2 L) ∧
    (F08.Thin8 L ∧ pRank 3 L = 1 ∧
      ∀ K ∈ calC D.M, F08.Thin8 K → pRank 3 K = 1 → K = L) ∧
    (∀ K ∈ calC D.M, ∀ n : ℕ, ¬ IsU3 (Bar2 K) (2 * n)) ∧
    (∃ g : G, g ∉ D.M ∧ 3 ∣ Nat.card ↥(L ⊓ conjSubgroup D.M g))

structure Ctx17_17 (D : Data G) (V₀ V L : Subgroup G) : Prop where
  hyp125 : Hyp125 D V₀ V
  mem_calC : L ∈ calC D.M
  sporadic : ∃ s : TauCeti.SporadicName, IsSpor (BarInf L) s
  counter : ¬ Concl17_17 D V₀ V L
  prefer : (∃ K ∈ calC D.M, (∃ s : TauCeti.SporadicName, IsSpor (BarInf K) s) ∧
      ¬ IsJ1 (Bar2 K) ∧ ¬ Concl17_17 D V₀ V K) → ¬ IsJ1 (Bar2 L)

@[expose] def R17_17At (D : Data G) (V₀ V : Subgroup G) : Prop :=
  ∀ L : Subgroup G, L ∈ calC D.M →
    (∃ s : TauCeti.SporadicName, IsSpor (BarInf L) s) → Concl17_17 D V₀ V L

@[expose] def R17_18At (D : Data G) (V₀ V : Subgroup G) : Prop :=
  ∀ L : Subgroup G, Ctx17_17 D V₀ V L →
    pRank 3 (CFSG.LocalAnalysis.UniquenessCase.UC22.conjClosure D.M L) ≤ 2

@[expose] def R17_19At (D : Data G) (V₀ V : Subgroup G) : Prop :=
  ∀ L : Subgroup G, Ctx17_17 D V₀ V L → ¬ IsJ1 (Bar2 L)

@[expose] def R17_20At (D : Data G) (V₀ V : Subgroup G) : Prop :=
  ∀ L : Subgroup G, Ctx17_17 D V₀ V L →
    pRank 3 L = 2 ∧ (L.subgroupOf D.M).Normal ∧
      ∃ s : TauCeti.SporadicName,
        (s = .M11 ∨ s = .M12 ∨ s = .M22 ∨ s = .M23 ∨ s = .M24 ∨
          s = .J2 ∨ s = .HS ∨ s = .He ∨ s = .Ru ∨ s = .J4) ∧ IsSpor (BarInf L) s

@[expose] def R17_21At (D : Data G) (V₀ V : Subgroup G) : Prop :=
  ∀ L : Subgroup G, Ctx17_17 D V₀ V L → D.k = 2

@[expose] def R17_22At (D : Data G) (V₀ V : Subgroup G) : Prop :=
  ∀ L P Z : Subgroup G, Ctx17_17 D V₀ V L →
    CFSG.ABGLocalTools.IsSylowOf 3 P L → Z = centerOf P →
      IsSpor (Bar2 L) .He ∨
        (IsSpor (Bar2 L) .J2 ∧ D.sig = {5} ∧
          ¬ rankThreeGamma 1 3 P ≤ D.M ∧ L = Opp 3 D.M ∧
          normalizer (Z : Set G) ≤ D.M ∧
          (conjSetOf (⊤ : Subgroup G) Z ∩ {X : Subgroup G | X ≤ D.M} = conjSetOf D.M Z) ∧
          Group.IsSolvable (centSection D.M L (pCoreOf 2 L)))

@[expose] def R17_23At (D : Data G) (V₀ V : Subgroup G) : Prop :=
  ∀ L : Subgroup G, Ctx17_17 D V₀ V L → IsSpor (Bar2 L) .J2

@[expose] def P17_24_1 (D : Data G) (V₀ V L : Subgroup G) (hV : IsElemAbelian 2 V) : Prop :=
  MBarGT D.M V₀ V 7 ∧ bBar L D.M V₀ V hV ≤ 3

@[expose] def P17_24_2 (D : Data G) (V₀ V L : Subgroup G) (hV : IsElemAbelian 2 V) : Prop :=
  IsIrrOn (barSub V₀ V hV L) ⊤ ⊥ ∧ rk (Vtil V₀ V hV) = 12 ∧
    mBar D.M V₀ V hV = 4 ∧ aBar D.M V₀ V hV = 2

@[expose] def R17_24At (D : Data G) (V₀ V : Subgroup G) : Prop :=
  ∀ L : Subgroup G, (c : Ctx17_17 D V₀ V L) →
    P17_24_1 D V₀ V L c.hyp125.isElemAbelian ∨
      P17_24_2 D V₀ V L c.hyp125.isElemAbelian

@[expose] def R17_25At (D : Data G) (V₀ V : Subgroup G) : Prop :=
  ∀ L : Subgroup G, (c : Ctx17_17 D V₀ V L) →
    P17_24_2 D V₀ V L c.hyp125.isElemAbelian

@[expose] def R17_26aAt (D : Data G) (V₀ V : Subgroup G) : Prop :=
  ∀ L : Subgroup G, Ctx17_17 D V₀ V L → mSub V₀ ≤ 4

@[expose] def P17_26b_1 (D : Data G) (V₀ V L : Subgroup G) (hV : IsElemAbelian 2 V) : Prop :=
  ∀ v : V, (v : G) ≠ 1 → (v : G) ∉ V₀ →
    pRank 5 ((D.M ⊓ centralizer ({(v : G)} : Set G)) ⊓ F11.CTilde D.M V₀ V : Subgroup G) = 1

@[expose] def P17_26b_2 (D : Data G) (V₀ V L : Subgroup G) (hV : IsElemAbelian 2 V) : Prop :=
  ∀ v : V, (v : G) ∉ V₀ →
    5 ∣ Nat.card ↥(MulAction.stabilizer (MulAut (Vtil V₀ V hV))
        (mkTil V₀ V hV (IntMod.mk hV v)) ⊓ Mbar D.M V₀ V hV) →
      1 < pRank 5 (D.M ⊓ centralizer ({(v : G)} : Set G) : Subgroup G)

@[expose] def P17_26b_3 (D : Data G) (V₀ V L : Subgroup G) (hV : IsElemAbelian 2 V) : Prop :=
  (4 + mSub V₀ : ℕ∞) ≤ rMV D.M V

@[expose] def R17_26b_1At (D : Data G) (V₀ V : Subgroup G) : Prop :=
  ∀ L : Subgroup G, (c : Ctx17_17 D V₀ V L) →
    P17_26b_1 D V₀ V L c.hyp125.isElemAbelian

@[expose] def R17_26b_2At (D : Data G) (V₀ V : Subgroup G) : Prop :=
  ∀ L : Subgroup G, (c : Ctx17_17 D V₀ V L) →
    P17_26b_2 D V₀ V L c.hyp125.isElemAbelian

@[expose] def R17_26b_3At (D : Data G) (V₀ V : Subgroup G) : Prop :=
  ∀ L : Subgroup G, (c : Ctx17_17 D V₀ V L) →
    P17_26b_3 D V₀ V L c.hyp125.isElemAbelian

@[expose] def R17_27At (D : Data G) (V₀ V : Subgroup G) : Prop :=
  ∀ L : Subgroup G, Ctx17_17 D V₀ V L →
    F12.Wi 0 D.T V ≤ F11.CTilde D.M V₀ V ∧
      normalizer ((F12.Wi 0 D.T V : Subgroup G) : Set G) ≤ D.M

@[expose] def R17_28At (D : Data G) (V₀ V : Subgroup G) : Prop :=
  ∀ L : Subgroup G, Ctx17_17 D V₀ V L →
    V₀ = ⊥ ∧ ¬ centralizer ((F12.Ci 2 D.T V : Subgroup G) : Set G) ≤ D.M

structure Ctx17_29 (D : Data G) (V₀ V L : Subgroup G) : Prop where
  ctx : Ctx17_17 D V₀ V L
  v0 : V₀ = ⊥

@[expose] def IsE4xA5B (X : Type) [Group X] : Prop :=
  Nonempty (X ≃* (Multiplicative (ZMod 2 × ZMod 2) × alternatingGroup (Fin 5)))

@[expose] noncomputable def jTbarB (D : Data G) (V₀ V : Subgroup G)
    (hV : IsElemAbelian 2 V) : Subgroup (MulAut (Vtil V₀ V hV)) :=
  (higherElemThompson (barSub V₀ V hV D.T) 0).map (barSub V₀ V hV D.T).subtype

@[expose] noncomputable def centBarLB (V₀ V L : Subgroup G) (hV : IsElemAbelian 2 V) (v : V) :
    Subgroup (MulAut (Vtil V₀ V hV)) :=
  MulAction.stabilizer (MulAut (Vtil V₀ V hV)) (mkTil V₀ V hV (IntMod.mk hV v)) ⊓
    barSub V₀ V hV L

@[expose] noncomputable def gammaOneABarB (D : Data G) (V₀ V A : Subgroup G) : Subgroup G :=
  ⨆ a ∈ A, ⨆ (_ : a ∉ F11.CTilde D.M V₀ V), V ⊓ centralizer ({a} : Set G)

@[expose] def P17_29_1 (D : Data G) (V₀ V L : Subgroup G) (hV : IsElemAbelian 2 V)
    (v₁ v₂ : V) : Prop :=
  (v₁ : G) ≠ 1 ∧ (v₂ : G) ≠ 1 ∧ (v₁ : G) ≠ (v₂ : G) ∧
    (¬ ∃ l ∈ L, l * (v₁ : G) * l⁻¹ = (v₂ : G)) ∧
    (∀ v : V, (v : G) ≠ 1 →
      (∃ l ∈ L, l * (v : G) * l⁻¹ = (v₁ : G)) ∨
        (∃ l ∈ L, l * (v : G) * l⁻¹ = (v₂ : G))) ∧
    centBarLB V₀ V L hV v₁ ≤
      normalizer (jTbarB D V₀ V hV : Set (MulAut (Vtil V₀ V hV))) ⊓ barSub V₀ V hV L ∧
    Nat.card ↥(centBarLB V₀ V L hV v₁) = 2 ^ 7 * 3 ∧
    IsE4xA5B (centBarLB V₀ V L hV v₂) ∧
    1 < pRank 5 (D.M ⊓ centralizer ({(v₂ : G)} : Set G) : Subgroup G) ∧
    centralizer ({(v₂ : G)} : Set G) ≤ D.M

@[expose] def P17_29_2 (D : Data G) (V₀ V L : Subgroup G) (hV : IsElemAbelian 2 V)
    (v₂ : V) : Prop :=
  ∀ t : MulAut (Vtil V₀ V hV), t ∈ Mbar D.M V₀ V hV → orderOf t = 2 →
    rk (commSub (⊤ : Subgroup (Vtil V₀ V hV)) (Subgroup.zpowers t)) < 6 →
      rk (commSub (⊤ : Subgroup (Vtil V₀ V hV)) (Subgroup.zpowers t)) = 4 ∧
        ∀ H : Subgroup (Vtil V₀ V hV), H ≤ fixV (Subgroup.zpowers t) →
          H.relIndex (fixV (Subgroup.zpowers t)) = 2 →
          ∃ l ∈ L, ∃ w : V, (w : G) = l * (v₂ : G) * l⁻¹ ∧
            mkTil V₀ V hV (IntMod.mk hV w) ∈ H

@[expose] def P17_29_3 (D : Data G) (V₀ V L : Subgroup G) (hV : IsElemAbelian 2 V)
    (v₂ : V) : Prop :=
  ∀ A : Subgroup G, A ≤ D.M → IsElemAbelian2 (barSub V₀ V hV A) →
    Nat.card ↥(barSub V₀ V hV A) = 16 → barSub V₀ V hV A ≤ barSub V₀ V hV D.T →
      ∃ l ∈ L, ∃ w : V, (w : G) = l * (v₂ : G) * l⁻¹ ∧
        (w : G) ∈ ⁅gammaOneABarB D V₀ V A, A⁆

@[expose] def R17_29_1At (D : Data G) (V₀ V : Subgroup G) : Prop :=
  ∀ L : Subgroup G, (c : Ctx17_29 D V₀ V L) →
    ∃ v₁ v₂ : V,
      P17_29_1 D V₀ V L c.ctx.hyp125.isElemAbelian v₁ v₂

@[expose] def R17_29_2At (D : Data G) (V₀ V : Subgroup G) : Prop :=
  ∀ L : Subgroup G, (c : Ctx17_29 D V₀ V L) → ∀ v₂ : V,
    (∃ v₁ : V, P17_29_1 D V₀ V L c.ctx.hyp125.isElemAbelian v₁ v₂) →
      P17_29_2 D V₀ V L c.ctx.hyp125.isElemAbelian v₂

@[expose] def R17_29_3At (D : Data G) (V₀ V : Subgroup G) : Prop :=
  ∀ L : Subgroup G, (c : Ctx17_29 D V₀ V L) → ∀ v₂ : V,
    (∃ v₁ : V, P17_29_1 D V₀ V L c.ctx.hyp125.isElemAbelian v₁ v₂) →
      P17_29_3 D V₀ V L c.ctx.hyp125.isElemAbelian v₂

@[expose] def R17_30At (D : Data G) (V₀ V : Subgroup G) : Prop :=
  ∀ L : Subgroup G, Ctx17_29 D V₀ V L → (6 : ℕ∞) ≤ rMV D.M V

@[expose] def R17_31At (D : Data G) (V₀ V : Subgroup G) : Prop :=
  ∀ L ∈ calC D.M,
    (∀ n : ℕ, ¬ CFSG.Quasithin.Is2F4 n (Bar2 L)) ∧
      ¬ LieModel (Bar2 L) .Tits 0 2 1

@[expose] def R17_32At (D : Data G) (V₀ V : Subgroup G) : Prop :=
  ∀ L ∈ calC D.M, ∀ n : ℕ, ¬ Is3D4 (Bar2 L) n

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17
