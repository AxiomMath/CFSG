module

public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.WeakClosure81.NineDefs
public import CFSG.Quasithin.Background.F7Basic
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.CGT.Timmesfeld75 Subgroup
open scoped Pointwise commutatorElement

@[expose] def Star915 {G : Type} [Group G] (V N L₁ L₂ : Subgroup G) : Prop :=
  ∀ g : G, g ∉ normalizer (V : Set G) → conjSubgroup V g ≤ normalizer (V : Set G) →
    ∀ x ∈ N ⊓ normalizer (conjSubgroup V g : Set G),
      (x ∈ L₁ ⊔ pCoreOf 2 N ∨ x ∈ L₂ ⊔ pCoreOf 2 N) → orderOf x ≠ 3

variable {X : Type} [Group X]

@[expose] def IsGood915 (L1b L2b : Subgroup X) (y : X) : Prop :=
  orderOf y = 3 ∧ (y ∈ L1b ∨ y ∈ L2b)

structure FiveWit (L1b L2b Tb A H R Lh : Subgroup X) : Prop where
  le : A ≤ H
  R_le : R ≤ H
  R_norm : H ≤ normalizer (R : Set X)
  R_le_T : R ≤ Tb
  idx : R.relIndex A = 2
  core : coreIn (Tb ⊓ centralizer (A : Set X)) Tb ≤ H
  Lh_le : Lh ≤ H
  Lh_norm : H ≤ normalizer (Lh : Set X)
  simple : IsSimpleGroup Lh
  inter : Lh ⊓ R = ⊥
  cent : H ⊓ centralizer (Lh : Set X) ≤ R
  good : ∃ y ∈ Lh, IsGood915 L1b L2b y
  pair : ∃ n ∈ H, IsPGroup 2 ↥(A ⊔ A.map (MulAut.conj n).toMonoidHom) ∧
    ∃ a ∈ A, ∃ b ∈ A, a * (n * b * n⁻¹) ≠ n * b * n⁻¹ * a

structure SevenWit (L1b L2b Tb A K Y : Subgroup X) : Prop where
  le : A ≤ K
  irr : TwoPTwoIrred K (K ⊓ Tb) Y 3
  core : coreIn (Tb ⊓ centralizer (A : Set X)) Tb ≤ K
  nonorm : ∀ R : Subgroup X, A ≤ R → R ≤ K ⊓ Tb →
    ¬ K ⊔ (Tb ⊓ normalizer ((K ⊓ Tb : Subgroup X) : Set X)) ≤ normalizer (R : Set X)
  good : ∃ y ∈ K, IsGood915 L1b L2b y

@[expose] def Kill761 (U K : Subgroup X) : Prop :=
  ∃ R : Subgroup X, pCoreOf 2 K ≤ R ∧ R ≤ K ∧ U ≤ normalizer (R : Set X) ∧
    Odd ((pCoreOf 2 K).relIndex R) ∧
    (∀ a ∈ U, (∀ x ∈ R, ⁅a, x⁆ ∈ pCoreOf 2 K) → a ∈ pCoreOf 2 K) ∧
    (pCoreOf 2 K).relIndex U ≠ 2

@[expose] def Kill763 (U K : Subgroup X) : Prop :=
  (pCoreOf 2 K).relIndex U = 2 ∧
    ∃ Y : Subgroup X, pCoreOf 2 K ≤ Y ∧ Y ≤ K ∧ U ≤ normalizer (Y : Set X) ∧
      Y ≤ ⁅Y, U⁆ ⊔ pCoreOf 2 K ∧
      (∀ a ∈ U, (∀ y ∈ Y, ⁅a, y⁆ ∈ pCoreOf 2 K) → a ∈ pCoreOf 2 K) ∧
      (∀ y ∈ Y, y ^ 3 ∈ pCoreOf 2 K) ∧ (∀ y ∈ Y, ∀ z ∈ Y, ⁅y, z⁆ ∈ pCoreOf 2 K) ∧
      (pCoreOf 2 K).relIndex Y ≠ 3

structure KillWit (L1b L2b Tb U K Y : Subgroup X) : Prop where
  le : U ≤ K
  irr : TwoPTwoIrred K (K ⊓ Tb) Y 3
  nonorm : ∀ R : Subgroup X, U ≤ R → R ≤ K ⊓ Tb →
    ¬ K ⊔ (Tb ⊓ normalizer ((K ⊓ Tb : Subgroup X) : Set X)) ≤ normalizer (R : Set X)
  good : ∃ y ∈ K, IsGood915 L1b L2b y
  kill : U ≤ pCoreOf 2 K ∨ Kill761 U K ∨ Kill763 U K

structure NineFifteenBarFacts (X : Type) [Group X] [Finite X] (L1b L2b Tb : Subgroup X) :
    Prop where
  le_of_normal : ∀ K : Subgroup X, K.Normal → (∃ x ∈ K, orderOf x = 2) → L1b ⊔ L2b ≤ K
  cent : centralizer ((L1b ⊔ L2b : Subgroup X) : Set X) = ⊥
  three : ∃ y ∈ L1b, orderOf y = 3
  pair : ∀ x : X, orderOf x = 2 → ∃ n : X,
    IsPGroup 2 (closure {x, n * x * n⁻¹}) ∧ x * (n * x * n⁻¹) ≠ (n * x * n⁻¹) * x
  table : ∀ A : Subgroup X, A ≤ Tb → IsElemAbelian 2 A → 4 ≤ Nat.card A →
    (∃ H R Lh : Subgroup X, FiveWit L1b L2b Tb A H R Lh) ∨
      ∃ K Y : Subgroup X, SevenWit L1b L2b Tb A K Y
  close : ∀ U E : Subgroup X, U ≤ E → E ≤ Tb → Tb ≤ normalizer (E : Set X) →
    IsElemAbelian 2 E → 4 ≤ Nat.card U →
    (∃ H R Lh : Subgroup X, FiveWit L1b L2b Tb U H R Lh) ∨
      ∃ K Y : Subgroup X, KillWit L1b L2b Tb U K Y

@[expose] def NGAbstract : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (V T N L₁ L₂ : Subgroup G), Hyp9 V T → T ≤ N →
    N ≤ normalizer (V : Set G) → L₁ ≤ N → L₂ ≤ N → Star915 V N L₁ L₂ →
    SevenSixThreeAbelian V →
    ∀ (X : Type) [Group X] [Finite X] (π : ↥N →* X), Function.Surjective π →
      (∀ x : ↥N, π x = 1 ↔ (x : G) ∈ pCoreOf 2 N) →
      NineFifteenBarFacts X ((L₁.subgroupOf N).map π) ((L₂.subgroupOf N).map π)
        ((T.subgroupOf N).map π) →
      normalizer (E3.wClos V 1 T : Set G) ≤ normalizer (V : Set G) ∨
        N ≤ normalizer (E3.wClos V 0 T : Set G)

end CFSG.LocalAnalysis.WeakClosure81
