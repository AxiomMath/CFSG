module

public import CFSG.Foundations.Basic
public import CFSG.GroupTheory.PCore.Construction
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.ChiefFactors.Core
public import CFSG.Open.LocalVocabulary
public import CFSG.Open.StatedDefs
public import CFSG.Blueprint.Catalog
public import CFSG.LargeExtraspecial.Timmesfeld.FStar
public import CFSG.LocalAnalysis.OddStandard.Solomon75GH71Defs
public import CFSG.LieType.Universal.Spin.Forms
public import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalGroup.Basic
public import CFSG.CGT.Timmesfeld75.Statements
public import CFSG.Foundations
public import CFSG.GroupTheory.LocalCores.Fitting
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.LBalanceComponentLifts
public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
public import CFSG.LocalAnalysis.ComponentInitial.LayerComponentOrbit
public import CFSG.LocalAnalysis.OddStandard.Solomon75Inputs
public import CFSG.LocalAnalysis.RankThreeUC.Asc1930
public import CFSG.LocalAnalysis.RankThreeUC.Notation
public import CFSG.Quasithin.Background.A1bGroups
public import CFSG.RankThree.PartOne.S10.ThetaContract
public import CFSG.RankThree.PartOne.S12.InputsBase

public section

namespace CFSG.RankThree.GF2n.Tim79a

open CFSG CFSG.Open
open CFSG.LargeExtraspecial.Timmesfeld (Qa IsExtraspecial2 HasWidth)

abbrev OMinusSixTwo : Type :=
  ↥(TauCeti.QuadraticMap.orthogonalGroup (CFSG.LieType.Universal.Spin.quadMinus 3 (ZMod 2) 1 1))

@[expose] def symThreeBlockBase : Subgroup (Equiv.Perm (Fin 3 ⊕ Fin 3)) :=
  Subgroup.closure {σ | ∀ a, (σ a).isLeft = a.isLeft}

@[expose] def symThreeWrTwo : Subgroup (Equiv.Perm (Fin 3 ⊕ Fin 3)) :=
  Subgroup.closure {σ | (∀ a, (σ a).isLeft = a.isLeft) ∨ ∀ a, (σ a).isLeft = !a.isLeft}

@[expose] def IsOmegaMinusSixByThree (K : Type) [Group K] : Prop :=
  ∃ (A C : Subgroup K) (x : K), (∀ a ∈ A, ∀ c ∈ C, Commute a c) ∧ A ⊓ C = ⊥ ∧
    Nonempty (↥A ≃* ↥(commutator OMinusSixTwo)) ∧ Nat.card C = 3 ∧
    A ⊔ C ⊔ Subgroup.zpowers x = ⊤ ∧
    Nonempty (↥(A ⊔ Subgroup.zpowers x) ≃* OMinusSixTwo) ∧
    Nonempty (↥(C ⊔ Subgroup.zpowers x) ≃* Equiv.Perm (Fin 3))

variable {G : Type} [Group G]

structure StrothHyp (z : G) (E F : Subgroup G) : Prop where
  orderOf_z : orderOf z = 2
  elemAbelian : IsElemAbelian 2 E
  two_le_card : 2 ≤ Nat.card E
  extraspecial : IsExtraspecial2 F
  mem_derived : z ∈ ⁅F, F⁆
  inf_eq_bot : E ⊓ F = ⊥
  commute : ∀ e ∈ E, ∀ f ∈ F, Commute e f
  sup_eq : E ⊔ F = Qa z
  centralizer_quotient : ∀ h : G, (h ∈ Subgroup.centralizer ({z} : Set G) ∧
    ∀ x ∈ Qa z, h * x * h⁻¹ * x⁻¹ ∈ centerIn (Qa z)) ↔ h ∈ Qa z

@[expose] def StrothCaseI (z : G) : Prop :=
  ∀ g : G, g * z * g⁻¹ ∈ Qa z → g * z * g⁻¹ ∈ centerIn (Qa z)

@[expose] def StrothCaseII (z : G) (w : ℕ) : Prop :=
  (∃ R : Subgroup G, R ≤ centerIn (Qa z) ∧ Nat.card (centerIn (Qa z)) = 2 * Nat.card R ∧
    ¬ Subgroup.centralizer (R : Set G) ≤
      (Subgroup.centralizer ({z} : Set G) ⊓ Subgroup.centralizer (R : Set G)) ⊔
        inSubgroup (pPrimeCore 2) (Subgroup.centralizer (R : Set G))) ∧
  (((∃ _ : (pCore 2 G).Normal,
        Nonempty (G ⧸ pCore 2 G ≃* Matrix.GeneralLinearGroup (Fin (w + 1)) (ZMod 2))) ∧
      IsElemAbelian 2 (pCore 2 G) ∧ Subgroup.center G ≤ pCore 2 G ∧
      Nat.card (pCore 2 G) = Nat.card (Subgroup.center G) * 2 ^ (w + 1)) ∨
    Nonempty (G ≃* Equiv.Perm (Fin 6)) ∨
    ∃ t : G, orderOf t = 2 ∧
      ¬ IsPGroup 2 (generalizedFitting (Subgroup.centralizer ({t} : Set G))))

@[expose] def StrothCaseIII (z : G) (w : ℕ) : Prop :=
  w = 2 ∧ ∃ _ : ((Qa z).subgroupOf (Subgroup.centralizer ({z} : Set G))).Normal,
    ∃ ι : (↥(Subgroup.centralizer ({z} : Set G)) ⧸
        (Qa z).subgroupOf (Subgroup.centralizer ({z} : Set G))) →* Equiv.Perm (Fin 3 ⊕ Fin 3),
      Function.Injective ι ∧ symThreeBlockBase ≤ ι.range ∧ ι.range ≤ symThreeWrTwo

@[expose] def StrothCaseIV (z : G) (w : ℕ) : Prop :=
  w = 3 ∧ (∃ _ : ((Qa z).subgroupOf (Subgroup.centralizer ({z} : Set G))).Normal,
      Nonempty ((↥(Subgroup.centralizer ({z} : Set G)) ⧸
        (Qa z).subgroupOf (Subgroup.centralizer ({z} : Set G))) ≃* alternatingGroup (Fin 8))) ∧
    Nat.card (centerIn (Qa z)) =
      Nat.card (centerIn (Subgroup.centralizer ({z} : Set G))) * 2 ^ 4

@[expose] def StrothCaseV (z : G) (w : ℕ) : Prop :=
  w = 4 ∧ (∃ _ : ((Qa z).subgroupOf (Subgroup.centralizer ({z} : Set G))).Normal,
      Nonempty ((↥(Subgroup.centralizer ({z} : Set G)) ⧸
        (Qa z).subgroupOf (Subgroup.centralizer ({z} : Set G))) ≃* OMinusSixTwo)) ∧
    (∀ h ∈ ⁅Subgroup.centralizer ({z} : Set G), Subgroup.centralizer ({z} : Set G)⁆,
      ∀ x ∈ centerIn (Qa z), Commute h x) ∧
    ¬ centerIn (Qa z) ≤ centerIn (Subgroup.centralizer ({z} : Set G))

@[expose] def StrothCaseVI (z : G) (w : ℕ) : Prop :=
  w = 4 ∧ (∃ _ : ((Qa z).subgroupOf (Subgroup.centralizer ({z} : Set G))).Normal,
      IsOmegaMinusSixByThree (↥(Subgroup.centralizer ({z} : Set G)) ⧸
        (Qa z).subgroupOf (Subgroup.centralizer ({z} : Set G))) ∧
      ∀ ρ : G, ∀ hρ : ρ ∈ Subgroup.centralizer ({z} : Set G), orderOf ρ = 3 →
        (QuotientGroup.mk (⟨ρ, hρ⟩ : ↥(Subgroup.centralizer ({z} : Set G))) :
            ↥(Subgroup.centralizer ({z} : Set G)) ⧸
              (Qa z).subgroupOf (Subgroup.centralizer ({z} : Set G))) ∈
          pCore 3 (↥(Subgroup.centralizer ({z} : Set G)) ⧸
            (Qa z).subgroupOf (Subgroup.centralizer ({z} : Set G))) →
        Nat.card (Subgroup.closure {y : G | ∃ x ∈ centerIn (Qa z), y = ρ * x * ρ⁻¹ * x⁻¹}) =
          4) ∧
    ∀ h ∈ ⁅⁅Subgroup.centralizer ({z} : Set G), Subgroup.centralizer ({z} : Set G)⁆,
        ⁅Subgroup.centralizer ({z} : Set G), Subgroup.centralizer ({z} : Set G)⁆⁆,
      ∀ x ∈ centerIn (Qa z), Commute h x

@[expose] def StrothCaseVII (z : G) (w : ℕ) : Prop :=
  w = 4 ∧ (∃ _ : ((Qa z).subgroupOf (Subgroup.centralizer ({z} : Set G))).Normal,
      Nonempty ((↥(Subgroup.centralizer ({z} : Set G)) ⧸
        (Qa z).subgroupOf (Subgroup.centralizer ({z} : Set G))) ≃* ↥(StatedSp 3 (ZMod 2)))) ∧
    (∀ N : Subgroup G, centerIn (Qa z) ≤ N → N ≤ Qa z →
      Subgroup.centralizer ({z} : Set G) ≤ Subgroup.normalizer (N : Set G) →
      N = centerIn (Qa z) ∨ N = Qa z) ∧
    centerIn (Subgroup.centralizer ({z} : Set G)) ≤ centerIn (Qa z) ∧
    Nat.card (centerIn (Qa z)) =
      Nat.card (centerIn (Subgroup.centralizer ({z} : Set G))) * 2 ^ 6

@[expose] def StrothCaseVIII (z : G) (w : ℕ) : Prop :=
  ∃ m : ℕ, w = 2 * m ∧ 2 < w ∧
    (∃ _ : ((Qa z).subgroupOf (Subgroup.centralizer ({z} : Set G))).Normal,
      Nonempty ((↥(Subgroup.centralizer ({z} : Set G)) ⧸
          (Qa z).subgroupOf (Subgroup.centralizer ({z} : Set G))) ≃*
        (↥(StatedSp m (ZMod 2)) × Equiv.Perm (Fin 3)))) ∧
    (∀ h ∈ ⁅⁅Subgroup.centralizer ({z} : Set G), Subgroup.centralizer ({z} : Set G)⁆,
        ⁅Subgroup.centralizer ({z} : Set G), Subgroup.centralizer ({z} : Set G)⁆⁆,
      ∀ x ∈ centerIn (Qa z), Commute h x) ∧
    ¬ centerIn (Qa z) ≤ centerIn (Subgroup.centralizer ({z} : Set G))

@[expose] def ParrottHyp (z : G) : Prop :=
  orderOf z = 2 ∧
    (∃ T F : Subgroup G, Nat.card T = 2 ∧ IsExtraspecial2 F ∧ Nat.card F = 2 ^ 9 ∧
      T ⊓ F = ⊥ ∧ (∀ t ∈ T, ∀ f ∈ F, Commute t f) ∧
      T ⊔ F = inSubgroup (pCore 2) (Subgroup.centralizer ({z} : Set G))) ∧
    ⁅inSubgroup (pCore 2) (Subgroup.centralizer ({z} : Set G)),
      inSubgroup (pCore 2) (Subgroup.centralizer ({z} : Set G))⁆ = Subgroup.zpowers z ∧
    Subgroup.centralizer ({z} : Set G) ⊓
        Subgroup.centralizer
          (inSubgroup (pCore 2) (Subgroup.centralizer ({z} : Set G)) : Set G) ≤
      inSubgroup (pCore 2) (Subgroup.centralizer ({z} : Set G)) ∧
    ∃ _ : ((inSubgroup (pCore 2) (Subgroup.centralizer ({z} : Set G))).subgroupOf
        (Subgroup.centralizer ({z} : Set G))).Normal,
      ∃ (X : Type) (_ : Group X), CFSG.Blueprint.LieModel X .PSp 2 3 1 ∧
        Nonempty ((↥(Subgroup.centralizer ({z} : Set G)) ⧸
          (inSubgroup (pCore 2) (Subgroup.centralizer ({z} : Set G))).subgroupOf
            (Subgroup.centralizer ({z} : Set G))) ≃* MulAut X)

@[expose] def ParrottCaseII (z : G) : Prop :=
  ∃ z₁ : G, z₁ ∈ centerIn (inSubgroup (pCore 2) (Subgroup.centralizer ({z} : Set G))) ∧
    z₁ ∉ Subgroup.zpowers z ∧ orderOf z₁ = 2 ∧ (Subgroup.zpowers z₁).Normal ∧
    ∃ G₀ : Subgroup G, G₀.index = 2 ∧ Subgroup.zpowers z₁ ≤ G₀ ∧
      ∃ _ : ((Subgroup.zpowers z₁).subgroupOf G₀).Normal, ∃ (X : Type) (_ : Group X),
        CFSG.Blueprint.LieModel X .PSU 6 2 1 ∧
          Nonempty ((↥G₀ ⧸ (Subgroup.zpowers z₁).subgroupOf G₀) ≃* X)

@[expose] def ParrottFi22Statement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (z : G), ParrottHyp z →
    Subgroup.centralizer ({z} : Set G) ⊔ pPrimeCore 2 G = ⊤ ∨ ParrottCaseII z ∨
      CFSG.Blueprint.NativeSporadic.IsSporadic G .Fi22

end CFSG.RankThree.GF2n.Tim79a

namespace CFSG.RankThree.GF2n.Tim79a

@[expose] def OMinusSixTwoAutPSp43Statement : Prop :=
  ∃ (X : Type) (_ : Group X), CFSG.Blueprint.LieModel X .PSp 2 3 1 ∧
    Nonempty (OMinusSixTwo ≃* MulAut X)

@[expose] def Fi22InvolutionCentralizerStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G], CFSG.Blueprint.NativeSporadic.IsSporadic G .Fi22 →
    ∀ t : G, orderOf t = 2 →
      Nat.card (Subgroup.centralizer ({t} : Set G)) = 18393661440 ∨
        Nat.card (Subgroup.centralizer ({t} : Set G)) = 53084160 ∨
        Nat.card (Subgroup.centralizer ({t} : Set G)) = 1769472

end CFSG.RankThree.GF2n.Tim79a
