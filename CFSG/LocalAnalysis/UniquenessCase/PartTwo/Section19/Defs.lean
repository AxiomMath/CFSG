module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.Defs
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.DefsModule
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.DefsWeakClosure
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Statements
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenDefs
public import CFSG.LocalAnalysis.UniquenessCase.UCFront12
public import CFSG.LocalAnalysis.UniquenessCase.UC22Lie
public import CFSG.LocalAnalysis.UniquenessCase.UCFront10
public import Certificates.Kernel.Sporadic.Fi22.C3151
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

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S19

open CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.UC22.F12
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

structure Hyp19 (D : Data G) (V₀ V : Subgroup G) (p : ℕ) (L : Subgroup G) : Prop where
  hyp125 : Hyp125 D V₀ V
  hp : p ∈ D.sig
  hL : L ∈ S17.calLp D p
  hX : conjClosure D.M L ∈ S17.calL0Star D p
  big : 1 < mSub V₀

theorem Hyp19.isElemAbelian {D : Data G} {V₀ V : Subgroup G} {p : ℕ} {L : Subgroup G}
    (h : Hyp19 D V₀ V p L) : IsElemAbelian 2 V :=
  (inCalV_of_hyp123 h.hyp125.1).2.2.2

@[expose] noncomputable def IOf (D : Data G) (p : ℕ) (L : Subgroup G) : Subgroup G :=
  if S17.jM D p = 4 then ⨆ K ∈ S17.calLp D p, K else conjClosure D.M L

@[expose] def Setting1910 (D : Data G) (V₀ V : Subgroup G) (p : ℕ) (L : Subgroup G) : Prop :=
  let n := S17.nOf L
  evenRank G = 3 ∧
    ((IsSp4 (Bar2 (IOf D p L)) n ∧ Odd n ∧ S17.SwapsParabolics D.T (IOf D p L) ∧
        (2 : ℤ) ^ n ≡ -1 [ZMOD (p : ℤ)]) ∨
      (IOf D p L = conjClosure D.M L ∧ conjClosure D.M L ≠ L ∧ 2 < n ∧
        ((IsL2 (Bar2 L) n ∧ (2 : ℤ) ^ n ≡ -1 [ZMOD (p : ℤ)]) ∨
          (IsSz (Bar2 L) n ∧ (2 : ℤ) ^ (2 * n) ≡ -1 [ZMOD (p : ℤ)]))) ∨
      ((S17.IsL2U3Product (Bar2 (IOf D p L)) n ∨ IsL2Square (Bar2 (IOf D p L)) n) ∧
        2 < n ∧ IsPowTwo n ∧ (2 : ℤ) ^ n ≡ -1 [ZMOD (p : ℤ)]))

structure Ctx19_1 (D : Data G) (V₀ V : Subgroup G) (p : ℕ) (L K : Subgroup G) : Prop where
  hyp : Hyp19 D V₀ V p L
  shape : IsL2 (Bar2 L) 2 ∨ IsU3 (Bar2 L) 2
  p_eq : p = 5
  hK : K ∈ calC D.M
  hKshape : IsAlt (Bar2 K) 5
  hLK : S17.Lp D 5 = L ⊔ K
  hne : K ≠ L

@[expose] def InNM2 (D : Data G) (I B R : Subgroup G) : Prop :=
  R ≤ D.M ∧ IsPGroup 2 R ∧ pCoreOf 2 I ≤ R ∧ B ≤ normalizer (R : Set G)

@[expose] def IsZModSq (X : Type) [Group X] (n : ℕ) : Prop :=
  Nonempty (X ≃* Multiplicative (ZMod (2 ^ n - 1) × ZMod (2 ^ n - 1)))

structure Ctx19_10 (D : Data G) (V₀ V : Subgroup G) (p : ℕ) (L : Subgroup G)
    (A : Subgroup G) (t : G) (B : Subgroup G) (r : ℕ) : Prop where
  hyp : Hyp19 D V₀ V p L
  h1910 : Setting1910 D V₀ V p L
  hA : A ≤ IOf D p L
  hAcard : IsZModSq A (S17.nOf L)
  hAT : Permutes A D.T
  htA : t ∈ IOf D p L
  ht2 : ∃ k : ℕ, orderOf t = 2 ^ k
  hinv : ∀ a ∈ A, t * a * t⁻¹ = a⁻¹
  hB : B = A ⊔ Subgroup.zpowers t
  hr : r ∈ piSet A
  hr5 : r ≠ 5

@[expose] def centModEl (V₀ : Subgroup G) (v : G) : Subgroup G where
  carrier := {m | m ∈ normalizer (V₀ : Set G) ∧ m * v * m⁻¹ * v⁻¹ ∈ V₀}
  one_mem' := ⟨Subgroup.one_mem _, by simp⟩
  mul_mem' := by
    rintro m₁ m₂ ⟨hm₁, h₁⟩ ⟨hm₂, h₂⟩
    refine ⟨Subgroup.mul_mem _ hm₁ hm₂, ?_⟩
    have hc₂ : m₂ * v * m₂⁻¹ * v⁻¹ ∈ V₀ := h₂
    have hconj : m₁ * (m₂ * v * m₂⁻¹ * v⁻¹) * m₁⁻¹ ∈ V₀ :=
      (Subgroup.mem_normalizer_iff.mp hm₁ _).mp hc₂
    have hmem : (m₁ * (m₂ * v * m₂⁻¹ * v⁻¹) * m₁⁻¹) * (m₁ * v * m₁⁻¹ * v⁻¹) ∈ V₀ :=
      V₀.mul_mem hconj h₁
    have hEq : m₁ * m₂ * v * (m₁ * m₂)⁻¹ * v⁻¹ =
        (m₁ * (m₂ * v * m₂⁻¹ * v⁻¹) * m₁⁻¹) * (m₁ * v * m₁⁻¹ * v⁻¹) := by group
    rw [hEq]
    exact hmem
  inv_mem' := by
    rintro m ⟨hm, h⟩
    refine ⟨Subgroup.inv_mem _ hm, ?_⟩
    have hmem : m⁻¹ * (m * v * m⁻¹ * v⁻¹)⁻¹ * m⁻¹⁻¹ ∈ V₀ :=
      (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hm) _).mp (V₀.inv_mem h)
    have hEq : m⁻¹ * (m * v * m⁻¹ * v⁻¹)⁻¹ * m⁻¹⁻¹ = m⁻¹ * v * m * v⁻¹ := by group
    rw [hEq] at hmem
    simpa using hmem

@[expose] def centModInM (D : Data G) (V₀ : Subgroup G) (v : G) : Subgroup G :=
  D.M ⊓ centModEl V₀ v

@[expose] def IsA6ModZ3 (X : Type) [Group X] : Prop :=
  CoverOf X (alternatingGroup (Fin 6)) ∧ Nat.card (Subgroup.center X) = 3

@[expose] def IsOmegaEps2 (X : Type) [Group X] (ε : Bool) (m : ℕ) : Prop :=
  if ε then IsOmegaPlus X (2 * m) 1 else IsOmegaMinus X (2 * m) 1

@[expose] def IsLieTypeOver2 (X : Type) [Group X] : Prop :=
  (∃ (t : CFSG.Assembly.LowTwoRank.StatedLieTag) (m : ℕ),
      CFSG.Assembly.LowTwoRank.StatedLieAdmissible t m 2 1 ∧
        CFSG.Blueprint.LieModel X t m 2 1) ∨
    IsAlt X 6 ∨ CFSG.Blueprint.LieModel X .PSU 3 3 1

@[expose] def IsNontrivialParabolic (X : Type) [Group X] (P : Subgroup X) : Prop :=
  IsParabolicTwo X P ∧ P ≠ ⊤ ∧ ∃ S : Sylow 2 X, normalizer (S : Set X) < P

@[expose] def IsCentralizerOfTransvectionIn (X : Type) [Group X] (m : ℕ)
    (Y : Subgroup X) : Prop :=
  ∃ τ : MulAut X, τ * τ = 1 ∧ τ ∉ (MulAut.conj : X →* MulAut X).range ∧
    (∀ y : X, y ∈ Y ↔ τ y = y) ∧
    Nat.card Y = if m = 3 then 720 else 1451520

@[expose] def muSet (D : Data G) (B : Subgroup G) : Set (Subgroup G) :=
  {Y | Y ≤ D.M ∧ Y = B ⊔ pCoreOf 2 Y ∧ pCoreOf 2 Y ≠ ⊥ ∧ calMOf Y ≠ {D.M}}

@[expose] def muStarSet (D : Data G) (B : Subgroup G) : Set (Subgroup G) :=
  {Y | Y ∈ muSet D B ∧ ∀ Z : Subgroup G, Z ∈ muSet D B → Y ≤ Z → Z = Y}

structure Ctx19_14 (D : Data G) (V₀ V : Subgroup G) (p : ℕ) (L : Subgroup G)
    (A : Subgroup G) (t : G) (B : Subgroup G) (r : ℕ)
    (Y N Dsub Hsub S : Subgroup G) : Prop where
  ctx : Ctx19_10 D V₀ V p L A t B r
  hY : Y ∈ muStarSet D B
  hN : N ∈ calMOf Y ∧ N ≠ D.M
  hD : Dsub ∈ calC N ∧ ¬ Dsub ≤ D.M
  hH : Hsub = Dsub ⊔ Y
  hS : S = pCoreOf 2 (Hsub ⊓ D.M)
  hO2 : pCoreOf 2 Dsub ≤ D.M

@[expose] def Oodd (H : Subgroup G) : Subgroup G :=
  (CFSG.pPrimeCore 2 ↥H).map H.subtype

@[expose] def ActsFaithfullyOn (V K : Subgroup G) : Prop :=
  V ⊓ centralizer (K : Set G) = ⊥

@[expose] def barOfInter (M L : Subgroup G) : Subgroup (Bar2 L) :=
  ((L ⊓ M).subgroupOf L).map (QuotientGroup.mk' (CFSG.pCore 2 ↥L))

@[expose] def P19_16_1 (D : Data G) (Dsub : Subgroup G) : Prop :=
  IsAlt (Bar2 Dsub) 10 ∧
    (Nonempty (↥(barOfInter D.M Dsub) ⧸ CFSG.pCore 2 ↥(barOfInter D.M Dsub) ≃*
        Equiv.Perm (Fin 3)) ∨
      Nonempty (↥(barOfInter D.M Dsub) ⧸ CFSG.pCore 2 ↥(barOfInter D.M Dsub) ≃*
        Equiv.Perm (Fin 5)) ∨
      Nonempty (↥(barOfInter D.M Dsub) ⧸ CFSG.pCore 2 ↥(barOfInter D.M Dsub) ≃*
        Equiv.Perm (Fin 6)))

@[expose] def P19_16_2 (D : Data G) (Dsub : Subgroup G) : Prop :=
  IsA6ModZ3 (Bar2 Dsub) ∧ (Dsub ⊓ D.M).relIndex Dsub = 15

@[expose] def P19_16_3 (D : Data G) (Dsub : Subgroup G) : Prop :=
  IsAlt (Bar2 Dsub) 7 ∧ (Dsub ⊓ D.M).relIndex Dsub = 35

@[expose] def P19_16_4 (D : Data G) (Dsub : Subgroup G) : Prop :=
  ∃ m : ℕ, (m = 3 ∨ m = 4) ∧
    ((∃ ε : Bool, IsOmegaEps2 (Bar2 Dsub) ε m ∧
        IsCentralizerOfTransvectionIn (Bar2 Dsub) m (barOfInter D.M Dsub)) ∨
      (IsAlt (Bar2 Dsub) (2 * m + 2) ∧
        ∃ (e : Bar2 Dsub ≃* alternatingGroup (Fin (2 * m + 2)))
          (a b : Fin (2 * m + 2)), a ≠ b ∧
          (barOfInter D.M Dsub).map e.toMonoidHom =
            (Subgroup.centralizer
              ({Equiv.swap a b} : Set (Equiv.Perm (Fin (2 * m + 2))))).comap
              (alternatingGroup (Fin (2 * m + 2))).subtype))

@[expose] def List19_16_5 (Q : Type) [Group Q] : Prop :=
  ((∃ m : ℕ, IsG2 Q m ∨ IsL3 Q m ∨ IsSp4 Q m ∨ IsU4 Q m ∨
      CFSG.Blueprint.LieModel Q .PSL 4 2 m ∨ CFSG.Blueprint.LieModel Q .PSp 3 2 m ∨
      IsOmega8m Q m) ∨
    (∃ s : ℕ, 5 ≤ s ∧ s ≤ 7 ∧ CFSG.Blueprint.LieModel Q .PSL s 2 1)) ∨
  IsAlt Q 6 ∨ CFSG.Blueprint.LieModel Q .PSU 3 3 1 ∨ IsU5 Q 2

@[expose] def P19_16_5 (D : Data G) (Dsub : Subgroup G) : Prop :=
  List19_16_5 (BarInf Dsub) ∧ IsNontrivialParabolic (Bar2 Dsub) (barOfInter D.M Dsub)

@[expose] def P19_16 (D : Data G) (Dsub : Subgroup G) : Prop :=
  P19_16_1 D Dsub ∨ P19_16_2 D Dsub ∨ P19_16_3 D Dsub ∨ P19_16_4 D Dsub ∨ P19_16_5 D Dsub

@[expose] def IsDynkinComponentFamily (D : Data G) (Dsub : Subgroup G) (d : ℕ)
    (K J : Fin d → Subgroup G) : Prop :=
  let O := pCoreOf 2 (Dsub ⊓ D.M)
  (∀ i, O ≤ K i ∧ K i ≤ Dsub ⊓ D.M ∧ ((K i).subgroupOf (Dsub ⊓ D.M)).Normal ∧
      K i = Opp 2 (K i) ⊔ O ∧ ¬ J i ≤ O) ∧
    (∀ i j : Fin d, i ≠ j → ⁅K i, K j⁆ ≤ O) ∧
    (⨆ i, K i) = Opp 2 (Dsub ⊓ D.M) ⊔ O ∧
    (∀ (i : Fin d) (A B : Subgroup G), O ≤ A → O ≤ B → A = Opp 2 A ⊔ O →
      B = Opp 2 B ⊔ O → A ⊔ B = K i → ⁅A, B⁆ ≤ O → A = K i ∨ B = K i) ∧
    (∀ i, J i = S17.oUpperTwo (K i))

@[expose] def P19_19_1 (D : Data G) (p : ℕ) (L J : Subgroup G) : Prop :=
  ∃ Li : Subgroup G, Li ∈ S17.calLp D p ∧ J ≤ Li ∧
    IsL2 (Bar2 J) (S17.nOf L) ∧
      (J ⊔ pCoreOf 2 Li = Li ∨ IsSp4 (Bar2 Li) (S17.nOf L) ∨
        IsU3 (Bar2 Li) (S17.nOf L))

@[expose] def P19_19_2 (D : Data G) (Dsub A J : Subgroup G) : Prop :=
  (J : Set G) ⊆ (pCoreOf 2 J : Set G) * (A : Set G) ∧
    (Nonempty (Bar2 J ≃* Multiplicative (ZMod 3)) ∨
      Nonempty (Bar2 J ≃* Multiplicative (ZMod 3 × ZMod 3))) ∧
      (IsLieTypeOver2 (BarInf Dsub) ∨ P19_16_1 D Dsub ∨ P19_16_2 D Dsub ∨ P19_16_3 D Dsub)

@[expose] def P19_19 (D : Data G) (p : ℕ) (L A Dsub J : Subgroup G) : Prop :=
  P19_19_1 D p L J ∨ P19_19_2 D Dsub A J

structure Ctx19_22 (D : Data G) (V₀ V : Subgroup G) (p : ℕ) (L : Subgroup G)
    (A : Subgroup G) (t : G) (B : Subgroup G) (r : ℕ) (A₀ : Subgroup G) : Prop where
  ctx : Ctx19_10 D V₀ V p L A t B r
  hA₀ : A₀ ≤ A
  hcard : Nat.card A₀ = r
  hcyc : IsCyclic A₀
  hcent : ¬ centralizer (A₀ : Set G) ≤ D.M
  hV₀ : V₀ ≤ centralizer (A₀ : Set G)

structure Ctx19_23 (D : Data G) (V₀ V : Subgroup G) (p : ℕ) (L : Subgroup G)
    (A : Subgroup G) (t : G) (B : Subgroup G) (r : ℕ) (A₀ H : Subgroup G) : Prop where
  ctx22 : Ctx19_22 D V₀ V p L A t B r A₀
  hH : H = centralizer (A₀ : Set G)
  hO2 : pCoreOf 2 H = ⊥

@[expose] def P19_29 (V : CFSG.LocalAnalysis.UniquenessCase.UC22.F10.LieAutVocab10)
    (K E A₀ S : Subgroup G) : Prop :=
  let N : Subgroup G := (K ⊔ E ⊔ (S ⊓ normalizer (K : Set G))) ⊓ normalizer (K : Set G)
  let f : ↥N →* MulAut ↥K :=
    (Subgroup.normalizerMonoidHom (H := K)).comp (Subgroup.inclusion inf_le_right)
  let CK : Subgroup ↥N := f.ker
  letI : CK.Normal := inferInstance
  let G₀ := ↥N ⧸ CK
  let Kbar : Subgroup G₀ := (K.subgroupOf N).map (QuotientGroup.mk' CK)
  let Ebar : Subgroup G₀ := (E.subgroupOf N).map (QuotientGroup.mk' CK)
  let Tbar : Subgroup G₀ := (S.subgroupOf N).map (QuotientGroup.mk' CK)
  (∃ q : ℕ, q.Prime ∧ q ≠ 2 ∧ IsChev Kbar q) ∨
    CFSG.LocalAnalysis.UniquenessCase.UC22.F10.IsJankoReeType10 Kbar ∨
    (IsChev Kbar 2 ∧ ∃ x ∈ Ebar, V.InducesField Kbar x) ∨
    (IsChev Kbar 2 ∧ (∀ x ∈ Ebar, ¬ V.InducesField Kbar x) ∧
      ∃ C : Subgroup G₀,
        CFSG.LocalAnalysis.UniquenessCase.UC22.F10.CartanActing10 (Kbar ⊔ Ebar) Tbar C ∧
          Ebar ≤ C)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S19
