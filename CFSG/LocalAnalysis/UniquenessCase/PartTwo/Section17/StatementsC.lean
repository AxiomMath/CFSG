module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.Defs
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.DefsModule
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.DefsWeakClosure
public import CFSG.LocalAnalysis.UniquenessCase.UC22S21a
public import CFSG.LocalAnalysis.UniquenessCase.UCFront08
public import CFSG.Blueprint.Catalog
public import CFSG.GroupTheory.ABGLocalTools.Basic
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
public import CFSG.GH74.BNPair.Defs
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
public import CFSG.Sporadic.Recognition.JankoWongPSLNine
public import CFSG.Sporadic.Schreier.J4SProfileNode
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PSL2NormalizedRootSylowCount

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17

open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22 CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.Open

variable {G : Type} [Group G] [Finite G]

@[expose] def CS17LieRank : CFSG.Open.StatedLieTag → ℕ → ℕ
  | .PSL, n => n - 1
  | .PSU, n => n / 2
  | .PSp, n => n
  | .POmegaOdd, n => n
  | .POmegaPlus, n => n
  | .POmegaMinus, n => n - 1
  | .G2, _ => 2
  | .F4, _ => 4
  | .E6, _ => 6
  | .E7, _ => 7
  | .E8, _ => 8
  | .twistedE6, _ => 4
  | .trialityD4, _ => 2
  | .twistedB2, _ => 1
  | .twistedF4, _ => 2
  | .twistedG2, _ => 1
  | .Tits, _ => 2

@[expose] def CIsChevOver (X : Type) [Group X] (n : ℕ) : Prop :=
  ∃ (t : CFSG.Open.StatedLieTag) (m : ℕ),
    CFSG.Open.StatedLieAdmissible t m 2 n ∧ CFSG.Blueprint.LieModel X t m 2 n

@[expose] def CHasLieRank (X : Type) [Group X] (l n : ℕ) : Prop :=
  ∃ (t : CFSG.Open.StatedLieTag) (m : ℕ),
    CFSG.Open.StatedLieAdmissible t m 2 n ∧ CFSG.Blueprint.LieModel X t m 2 n ∧
      CS17LieRank t m = l

@[expose] def CIsCartanOf (T L C : Subgroup G) : Prop :=
  C ≤ L ∧ OInf L ≤ C ∧ C ≤ normalizer ((T ⊓ L : Subgroup G) : Set G) ∧
    Odd ((OInf L).relIndex C) ∧
    ∃ k : ℕ, C.relIndex (L ⊓ normalizer ((T ⊓ L : Subgroup G) : Set G)) = 2 ^ k

@[expose] def CIsCosetReps (H K : Subgroup G) (Γ : Set G) : Prop :=
  Γ ⊆ K ∧ ∀ k ∈ K, ∃! γ : G, γ ∈ Γ ∧ ∃ h ∈ H, k = h * γ

structure CNatModStructSU3Sub (W : Type) [Group W] (W' : Subgroup W)
    (X : Subgroup (MulAut W)) (n : ℕ) where
  K : Type
  [fieldK : Field K]
  [finiteK : Finite K]
  cardK : Nat.card K = (2 ^ n) ^ 2
  e : ↥W' ≃* Multiplicative (Fin 3 → K)
  invariant : ∀ x ∈ X, ∀ w ∈ W', x w ∈ W'
  map_mem : ∀ x ∈ X, ∃ A ∈ CFSG.Open.StatedSU 3 (2 ^ n) K,
    ∀ (w : W) (hw : w ∈ W') (hxw : x w ∈ W'),
      e ⟨x w, hxw⟩ = Multiplicative.ofAdd ((A : Matrix (Fin 3) (Fin 3) K).mulVec
        (Multiplicative.toAdd (e ⟨w, hw⟩)))
  surj : ∀ A ∈ CFSG.Open.StatedSU 3 (2 ^ n) K, ∃ x ∈ X,
    ∀ (w : W) (hw : w ∈ W') (hxw : x w ∈ W'),
      e ⟨x w, hxw⟩ = Multiplicative.ofAdd ((A : Matrix (Fin 3) (Fin 3) K).mulVec
        (Multiplicative.toAdd (e ⟨w, hw⟩)))
  faithful : ∀ x ∈ X, (∀ w ∈ W', x w = w) → x = 1

@[expose] def CNatModSU3Sub (W : Type) [Group W] (W' : Subgroup W)
    (X : Subgroup (MulAut W)) (n : ℕ) : Prop :=
  Nonempty (CNatModStructSU3Sub W W' X n)

abbrev CNatModStructSU3 (W : Type) [Group W] (X : Subgroup (MulAut W)) (n : ℕ) :=
  CNatModStructSU3Sub W ⊤ X n

@[expose] def CNatModSU3 (W : Type) [Group W] (X : Subgroup (MulAut W)) (n : ℕ) : Prop :=
  CNatModSU3Sub W ⊤ X n

@[expose] def CNonsingular (W : Type) [Group W] {X : Subgroup (MulAut W)}
    (S : CNatModStructSU3 W X 2) (v : W) : Prop :=
  letI : Field S.K := S.fieldK
  (∑ i : Fin 3, (Multiplicative.toAdd (S.e ⟨v, Subgroup.mem_top v⟩) i) ^ 4 *
    (Multiplicative.toAdd (S.e ⟨v, Subgroup.mem_top v⟩) i)) ≠ 0

structure Ctx17_33 (D : Data G) (V₀ V L : Subgroup G) (n : ℕ) : Prop where
  hyp125 : Hyp125 D V₀ V
  mem_calC : L ∈ calC D.M
  shape : IsSU3 (Bar2 L) n
  counter : ¬ (IsPowTwo n ∧ 1 < mSub V₀)

structure Ctx17_40 (D : Data G) (V₀ V L : Subgroup G) (n : ℕ) : Prop where
  ctx : Ctx17_33 D V₀ V L n
  v0 : V₀ = ⊥

@[expose] def P17_42_more (D : Data G) (X : Subgroup G) (n : ℕ) : Prop :=
  evenRank G = 3 ∧
    ∀ r : ℕ, r.Prime → 5 < r → r ∣ 2 ^ n - 1 →
      X = Opp r D.M ∧
        ∀ E : Subgroup G, E ≤ X → IsElemAbelian r E → Nat.card E = r ^ 2 →
          E ∈ CFSG.LocalAnalysis.RankThreeUC.uniqueSet D.M

@[expose] def P17_42_1 (D : Data G) (X : Subgroup G) : Prop :=
  F08.Thin8 X ∨ (∃ n : ℕ, IsU3 (Bar2 X) n) ∨ IsL3 (Bar2 X) 2

@[expose] def P17_42_2 (D : Data G) (L X : Subgroup G) (p : ℕ) : Prop :=
  ∃ (n : ℕ) (x : G), x ∈ D.M ∧ X = L ⊔ CFSG.Quasithin.conjSubgroup L x ∧ X ≠ L ∧
    ((IsL2 (Bar2 L) n ∧ (2 : ℤ) ^ n ≡ -1 [ZMOD (p : ℤ)]) ∨
      (IsSz (Bar2 L) n ∧ (2 : ℤ) ^ (2 * n) ≡ -1 [ZMOD (p : ℤ)])) ∧
    P17_42_more D X n

@[expose] def P17_42_3 (D : Data G) (X : Subgroup G) (p : ℕ) : Prop :=
  ∃ n : ℕ, IsU5 (Bar2 X) n ∧ n = 2 ∧ D.k = 2 ∧ p = 5 ∧ P17_42_more D X n

@[expose] def P17_42_4 (D : Data G) (X : Subgroup G) (p : ℕ) : Prop :=
  ∃ n : ℕ, (IsSp4 (Bar2 X) n ∨ IsG2 (Bar2 X) n) ∧ 1 < n ∧ Odd n ∧
    (2 : ℤ) ^ n ≡ -1 [ZMOD (p : ℤ)] ∧ D.k = 1 ∧ P17_42_more D X n

@[expose] def P17_42_5 (D : Data G) (X : Subgroup G) (p : ℕ) : Prop :=
  ∃ n : ℕ, IsU4 (Bar2 X) n ∧ 1 < n ∧
    (2 : ℤ) ^ n ≡ -1 [ZMOD (p : ℤ)] ∧ P17_42_more D X n

@[expose] def Concl17_42 (D : Data G) (L X : Subgroup G) (p : ℕ) : Prop :=
  P17_42_1 D X ∨ P17_42_2 D L X p ∨ P17_42_3 D X p ∨ P17_42_4 D X p ∨ P17_42_5 D X p

structure Ctx17_42 (D : Data G) (V₀ V L X : Subgroup G) (p : ℕ)
    (n l : ℕ) (C Dc : Subgroup G) (Gamma : Set G) : Prop where
  hyp125 : Hyp125 D V₀ V
  mem_calC : L ∈ calC D.M
  X_eq : X = conjClosure D.M L
  p_mem : p ∈ D.sig
  counter : ¬ Concl17_42 D L X p
  chev : CIsChevOver (BarInf L) n
  rank : CHasLieRank (BarInf L) l n
  cartan : CIsCartanOf D.T L C
  reps : CIsCosetReps ((D.M ⊓ normalizer ((D.T ⊓ X : Set G))) ⊓ normalizer (L : Set G))
    (D.M ⊓ normalizer ((D.T ⊓ X : Set G))) Gamma
  Dc_eq : Dc = ⨆ x ∈ Gamma, CFSG.Quasithin.conjSubgroup C x

@[expose] def R17_33_2At (D : Data G) (V₀ V : Subgroup G) : Prop :=
  ∀ (L : Subgroup G) (n : ℕ), L ∈ calC D.M → IsSU3 (Bar2 L) n → IsPowTwo n

@[expose] def R17_33_2 (D : Data G) : Prop :=
  ∀ (V₀ V : Subgroup G) (_hV : Hyp125 D V₀ V), R17_33_2At D V₀ V

@[expose] def R17_33_3At (D : Data G) (V₀ V : Subgroup G) : Prop :=
  ∀ (L : Subgroup G) (n : ℕ), L ∈ calC D.M → IsSU3 (Bar2 L) n → 1 < mSub V₀

@[expose] def R17_34_1At (D : Data G) (V₀ V : Subgroup G) : Prop :=
  ∀ (L : Subgroup G) (n : ℕ) (c : Ctx17_33 D V₀ V L n),
    bBar (conjClosure D.M L) D.M V₀ V c.hyp125.isElemAbelian ≤ n

@[expose] def R17_34_2At (D : Data G) (V₀ V : Subgroup G) : Prop :=
  ∀ (L : Subgroup G) (n : ℕ) (c : Ctx17_33 D V₀ V L n),
    mBar D.M V₀ V c.hyp125.isElemAbelian ≤ 2 * n + D.k

@[expose] def R17_34_3At (D : Data G) (V₀ V : Subgroup G) : Prop :=
  ∀ (L : Subgroup G) (n : ℕ) (c : Ctx17_33 D V₀ V L n),
    V₀ = ⊥ → mBar D.M V₀ V c.hyp125.isElemAbelian ≤ n + D.k

@[expose] def R17_34At (D : Data G) (V₀ V : Subgroup G) : Prop :=
  R17_34_1At D V₀ V ∧ R17_34_2At D V₀ V ∧ R17_34_3At D V₀ V

@[expose] def R17_35_1At (D : Data G) (V₀ V : Subgroup G) : Prop :=
  ∀ (L : Subgroup G) (n : ℕ) (c : Ctx17_33 D V₀ V L n),
    CNatModSU3Sub (Vtil V₀ V c.hyp125.isElemAbelian)
        (CFSG.Quasithin.commSub (⊤ : Subgroup (Vtil V₀ V c.hyp125.isElemAbelian))
          (barSub V₀ V c.hyp125.isElemAbelian L))
        (barSub V₀ V c.hyp125.isElemAbelian L) n ∧
      mBar D.M V₀ V c.hyp125.isElemAbelian = 2 * n

@[expose] def R17_35_2At (D : Data G) (V₀ V : Subgroup G) : Prop :=
  ∀ (L : Subgroup G) (n : ℕ) (c : Ctx17_33 D V₀ V L n),
    V₀ = ⊥ →
      IsU3 ↥(barSub V₀ V c.hyp125.isElemAbelian (conjClosure D.M L)) 2 ∧
        D.k = 2 ∧ mBar D.M V₀ V c.hyp125.isElemAbelian = 4 ∧ L = conjClosure D.M L

@[expose] def R17_35At (D : Data G) (V₀ V : Subgroup G) : Prop :=
  R17_35_1At D V₀ V ∧ R17_35_2At D V₀ V

@[expose] def R17_36aAt (D : Data G) (V₀ V : Subgroup G) : Prop :=
  ∀ (L : Subgroup G) (n : ℕ) (_c : Ctx17_33 D V₀ V L n), L = conjClosure D.M L

@[expose] def R17_36bAt (D : Data G) (V₀ V : Subgroup G) : Prop :=
  ∀ (L : Subgroup G) (n : ℕ) (_c : Ctx17_33 D V₀ V L n),
    ∀ r : ℕ, r.Prime → r ∣ 2 ^ n - 1 → ∀ X : Subgroup G,
      Nat.card X = r → X ≤ L → normalizer (X : Set G) ≤ D.M

@[expose] def R17_37At (D : Data G) (V₀ V : Subgroup G) : Prop :=
  ∀ (L : Subgroup G) (n : ℕ) (_c : Ctx17_33 D V₀ V L n), IsPowTwo n

@[expose] def R17_38At (D : Data G) (V₀ V : Subgroup G) : Prop :=
  ∀ (L : Subgroup G) (n : ℕ) (_c : Ctx17_33 D V₀ V L n), mSub V₀ ≤ 1

@[expose] def R17_39At (D : Data G) (V₀ V : Subgroup G) : Prop :=
  ∀ (L : Subgroup G) (n : ℕ) (_c : Ctx17_33 D V₀ V L n), V₀ = ⊥

@[expose] def R17_40At (D : Data G) (V₀ V : Subgroup G) : Prop :=
  ∀ (L : Subgroup G) (n : ℕ) (c : Ctx17_40 D V₀ V L n),
    barSub V₀ V c.ctx.hyp125.isElemAbelian L =
        barSub V₀ V c.ctx.hyp125.isElemAbelian (Opp 5 D.M) ∧
      IsU3 ↥(barSub V₀ V c.ctx.hyp125.isElemAbelian L) 2 ∧ D.sig = {5}

@[expose] def R17_41_1At (D : Data G) (V₀ V : Subgroup G) : Prop :=
  ∀ (L : Subgroup G) (n : ℕ) (_c : Ctx17_40 D V₀ V L n),
    5 ∈ piSet (D.M ⊓ centralizer (V : Set G))

@[expose] def R17_41_3At (D : Data G) (V₀ V : Subgroup G) : Prop :=
  ∀ (L : Subgroup G) (n : ℕ) (_c : Ctx17_40 D V₀ V L n),
    (8 : ℕ∞) ≤ rMV D.M V

@[expose] def R17_42At (D : Data G) (V₀ V : Subgroup G) : Prop :=
  ∀ (L : Subgroup G) (p : ℕ), L ∈ calC D.M → p ∈ D.sig →
    Concl17_42 D L (conjClosure D.M L) p

@[expose] def R17_42 (D : Data G) : Prop :=
  ∀ (V₀ V : Subgroup G) (_hV : Hyp125 D V₀ V), R17_42At D V₀ V

@[expose] def R17_43At (D : Data G) (V₀ V : Subgroup G) : Prop :=
  ∀ (L X : Subgroup G) (p n l : ℕ) (C Dc : Subgroup G) (Gamma : Set G),
    Ctx17_42 D V₀ V L X p n l C Dc Gamma → 2 < 2 ^ n

@[expose] def R17_44_1At (D : Data G) (V₀ V : Subgroup G) : Prop :=
  ∀ (L X : Subgroup G) (p n l : ℕ) (C Dc : Subgroup G) (Gamma : Set G),
    Ctx17_42 D V₀ V L X p n l C Dc Gamma →
      ∀ r : ℕ, r.Prime → r ≠ 2 → CFSG.Open.pRank r Dc ≤ 3

@[expose] def R17_44_2At (D : Data G) (V₀ V : Subgroup G) : Prop :=
  ∀ (L X : Subgroup G) (p n l : ℕ) (C Dc : Subgroup G) (Gamma : Set G),
    Ctx17_42 D V₀ V L X p n l C Dc Gamma →
      ∀ r : ℕ, r.Prime → 5 < r →
        (evenRank G = 3 ∨ CFSG.RankThree.PartOne.IsStronglyPEmbedded r D.M) →
          CFSG.Open.pRank r Dc ≤ 2

@[expose] def R17_44_3At (D : Data G) (V₀ V : Subgroup G) : Prop :=
  ∀ (L X : Subgroup G) (p n l : ℕ) (C Dc : Subgroup G) (Gamma : Set G),
    Ctx17_42 D V₀ V L X p n l C Dc Gamma →
      CFSG.Open.pRank 3 Dc ≤ 2 ∧
        ((D.k = 1 ∨ 2 < CFSG.Open.pRank 3 X) → CFSG.Open.pRank 3 Dc ≤ 1)

@[expose] def R17_45At (D : Data G) (V₀ V : Subgroup G) : Prop :=
  ∀ (L X : Subgroup G) (p n l : ℕ) (C Dc : Subgroup G) (Gamma : Set G),
    Ctx17_42 D V₀ V L X p n l C Dc Gamma → 1 < l

@[expose] def R17_46At (D : Data G) (V₀ V : Subgroup G) : Prop :=
  ∀ (L X : Subgroup G) (p n l : ℕ) (C Dc : Subgroup G) (Gamma : Set G),
    Ctx17_42 D V₀ V L X p n l C Dc Gamma → l = 2

@[expose] def R17_47At (D : Data G) (V₀ V : Subgroup G) : Prop :=
  ∀ (L X : Subgroup G) (p n l : ℕ) (C Dc : Subgroup G) (Gamma : Set G),
    Ctx17_42 D V₀ V L X p n l C Dc Gamma → ¬ IsL3 (BarInf L) n

@[expose] def R17_48At (D : Data G) (V₀ V : Subgroup G) : Prop :=
  ∀ (L X : Subgroup G) (p n l : ℕ) (C Dc : Subgroup G) (Gamma : Set G),
    Ctx17_42 D V₀ V L X p n l C Dc Gamma → ¬ IsU5 (BarInf L) n

@[expose] def R17_49At (D : Data G) (V₀ V : Subgroup G) : Prop :=
  ∀ (L X : Subgroup G) (p n l : ℕ) (C Dc : Subgroup G) (Gamma : Set G),
    Ctx17_42 D V₀ V L X p n l C Dc Gamma → L = X

@[expose] def R17_50At (D : Data G) (V₀ V : Subgroup G) : Prop :=
  ∀ (L X : Subgroup G) (p n l : ℕ) (C Dc : Subgroup G) (Gamma : Set G),
    Ctx17_42 D V₀ V L X p n l C Dc Gamma →
      (IsU4 (Bar2 X) n ∨ IsSp4 (Bar2 X) n ∨ IsG2 (Bar2 X) n) ∧ 2 < 2 ^ n

@[expose] def R17_51At (D : Data G) (V₀ V : Subgroup G) : Prop :=
  ∀ (L X : Subgroup G) (p n l : ℕ) (C Dc : Subgroup G) (Gamma : Set G),
    Ctx17_42 D V₀ V L X p n l C Dc Gamma →
      ∀ r : ℕ, r.Prime → r ∣ 2 ^ n - 1 → ∀ R : Subgroup G,
        CFSG.ABGLocalTools.IsSylowOf r R C → ¬ rankThreeGamma 1 r R ≤ D.M

@[expose] def R17_52_1At (D : Data G) (V₀ V : Subgroup G) : Prop :=
  ∀ (L X : Subgroup G) (p n l : ℕ) (C Dc : Subgroup G) (Gamma : Set G),
    Ctx17_42 D V₀ V L X p n l C Dc Gamma → eM D.M = 3

@[expose] def R17_52_2At (D : Data G) (V₀ V : Subgroup G) : Prop :=
  ∀ (L X : Subgroup G) (p n l : ℕ) (C Dc : Subgroup G) (Gamma : Set G),
    Ctx17_42 D V₀ V L X p n l C Dc Gamma →
      CFSG.Open.pRank p L = 2 ∨
        (IsU4 (Bar2 L) n ∧ (2 : ℤ) ^ n ≡ -1 [ZMOD (p : ℤ)])

@[expose] def R17_52_3At (D : Data G) (V₀ V : Subgroup G) : Prop :=
  ∀ (L X : Subgroup G) (p n l : ℕ) (C Dc : Subgroup G) (Gamma : Set G),
    Ctx17_42 D V₀ V L X p n l C Dc Gamma →
      (2 : ℤ) ^ n ≡ -1 [ZMOD (p : ℤ)]

@[expose] def R17_52At (D : Data G) (V₀ V : Subgroup G) : Prop :=
  R17_52_1At D V₀ V ∧ R17_52_2At D V₀ V ∧ R17_52_3At D V₀ V

@[expose] def R17_53At (D : Data G) (V₀ V : Subgroup G) : Prop :=
  ∀ (L X : Subgroup G) (p n l : ℕ) (C Dc : Subgroup G) (Gamma : Set G),
    Ctx17_42 D V₀ V L X p n l C Dc Gamma →
      ∀ r : ℕ, r.Prime → 5 < r → r ∣ 2 ^ n - 1 → L = Opp r D.M

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17
