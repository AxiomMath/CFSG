module

public import CFSG.RankThree.PartTwo.Sec15.Item15Inputs
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Monster.B.TwoA.Census.PermClasses
public import CFSG.RankThree.PartTwo.Sec13.Item13Basic
public import CFSG.RankThree.PartTwo.Sec15.Item15Steps
public import CFSG.RankThree.PartTwo.Sec16.Notation
public import CFSG.Sporadic.Suz.Simple

public section

namespace CFSG.RankThree.PartTwo.Sec14

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec15

@[expose] noncomputable def Item1411_3R : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec15R G A c L → Item1411_3 A (lB A)

end CFSG.RankThree.PartTwo.Sec14

namespace CFSG.RankThree.PartTwo.Sec15

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14

@[expose] noncomputable def Item1510R : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec15R G A c L → Item1510 A

@[expose] noncomputable def Item14_23R : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec15R G A c L → Item14_23 A L

end CFSG.RankThree.PartTwo.Sec15

namespace CFSG.RankThree.PartTwo.Sec16

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec15
  CFSG.GH74.GLS
open CFSG.Assembly.RankThreeEven (projSL projSU)

section Vocabulary

variable {G : Type} [Group G] [Finite G]

@[expose] noncomputable def thetaCen (X : Set G) : Subgroup G :=
  inSubgroup (aschbacherSolvableCore 3) (Subgroup.centralizer X)

@[expose] noncomputable def IsZ3LThreeTwo (A : Subgroup G) (c : G) (L : Subgroup G) (n : ℕ) :
    Prop :=
  1 ≤ n ∧ Sec4.IsoLThreePi (↥L ⧸ aschbacherSolvableCore 3 ↥L) 2 n ∧
    Nonempty (lBarA c L A ≃* Multiplicative (ZMod 3) × Sec12.lBar c L)

@[expose] noncomputable def Concl1611 (A : Subgroup G) (c : G) (L : Subgroup G) : Prop :=
  Sec8.IsZ3PGLThreePi ↥(lBarA c L A) ∨ ∃ n : ℕ, IsZ3LThreeTwo A c L n

@[expose] noncomputable def Concl1612 (A : Subgroup G) (c : G) (L : Subgroup G) : Prop :=
  (IsSimpleGroup ↥L ∧
      ∀ T ∈ invariantPiSubgroups (Subgroup.centralizer (L : Set G)) A (piOf 2), T = ⊥) ∨
    Nonempty (lBarA c L A ≃* Multiplicative (ZMod 3) × projSL 3 (GaloisField 2 2))

end Vocabulary

structure Ctx169 (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G) :
    Prop extends Sec15R G A c L where
  scriptY0_eq : scriptY0 A (lB A) = ∅

@[expose] noncomputable def Step1610 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Ctx169 G A c L → scriptY3 A (lB A) = scriptY1 A (lB A)

@[expose] noncomputable def Step1611 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Ctx169 G A c L → Concl1611 A c L

@[expose] noncomputable def Step1611List : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G)
    (h : Sec15R G A c L), Item142 A (lB A) c L h.isElemAbelian.1 h.mem_A →
      ¬ Concl1611 A c L →
        ¬ TransOn A (lB A) (xA A) (Subgroup.normalizer (Subgroup.zpowers c : Set G))

@[expose] noncomputable def Step1612 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Ctx169 G A c L → Concl1612 A c L

@[expose] noncomputable def Step1612NotSimple : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Ctx169 G A c L → ¬ IsSimpleGroup ↥L →
      IsEmpty (lBarA c L A ≃* Multiplicative (ZMod 3) × projSL 3 (GaloisField 2 2)) →
        ∃ T ∈ invariantPiSubgroups ⊤ (A ⊔ L) (piOf 2), T ≠ ⊥

@[expose] noncomputable def Step1612Y3 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Ctx169 G A c L →
      IsEmpty (lBarA c L A ≃* Multiplicative (ZMod 3) × projSL 3 (GaloisField 2 2)) →
      ∀ T ∈ invariantPiSubgroups ⊤ (A ⊔ L) (piOf 2), T ≠ ⊥ →
        ∃ Y ∈ scriptY3 A (lB A), oPrimeResidualOf 3 Y ≠ ⊥

@[expose] noncomputable def Step1613 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Ctx169 G A c L → ∀ D : Subgroup G, D ≤ A ⊓ L → Nat.card D = 3 →
      Subgroup.normalizer ((D ⊔ Subgroup.zpowers c : Subgroup G) : Set G) ⊓
          Subgroup.normalizer (D : Set G) ≤
        Subgroup.normalizer (Subgroup.zpowers c : Set G)

@[expose] noncomputable def Step1614 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Ctx169 G A c L → omegaA A = {Subgroup.zpowers c}

@[expose] noncomputable def Step1615 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Ctx169 G A c L → Sec8.IsZ3PGLThreePi ↥(lBarA c L A) →
      (∀ b ∈ Subgroup.zpowers c ⊔ (A ⊓ L), b ≠ 1 → Odd (Nat.card (thetaCen ({b} : Set G)))) ∧
        Odd (Nat.card (thetaCen ((Subgroup.zpowers c ⊔ (A ⊓ L) : Subgroup G) : Set G)))

@[expose] noncomputable def KS1615Meet : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Ctx169 G A c L → Sec8.IsZ3PGLThreePi ↥(lBarA c L A) → A ⊓ L ≠ ⊥

@[expose] noncomputable def Step1616 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Ctx169 G A c L → ∃ n : ℕ, IsZ3LThreeTwo A c L n

@[expose] noncomputable def Step1616Fix : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Ctx169 G A c L → Sec8.IsZ3PGLThreePi ↥(lBarA c L A) →
      ∀ S ∈ scriptQPiStar A (lB A) ⊤ (piOf 2), ⁅S, Subgroup.zpowers c⁆ = ⊥ →
        ⁅S, A⁆ = ⊥ ∨
          ¬ Odd (Nat.card (thetaCen ((Subgroup.zpowers c ⊔ (A ⊓ L) : Subgroup G) : Set G)))

@[expose] noncomputable def Step1616Comm : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Ctx169 G A c L → ∀ S ∈ scriptQPiStar A (lB A) ⊤ (piOf 2), ⁅S, A⁆ = ⊥ →
      ∀ a ∈ A, a ≠ 1 → Odd (Nat.card (⁅thetaCen ({a} : Set G), A⁆ : Subgroup G))

@[expose] noncomputable def Step1616Omega : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Ctx169 G A c L → Sec8.IsZ3PGLThreePi ↥(lBarA c L A) →
      ∀ S ∈ scriptQPiStar A (lB A) ⊤ (piOf 2), ∀ b ∈ Subgroup.zpowers c ⊔ (A ⊓ L), b ≠ 1 →
        Odd (Nat.card (thetaCen ({b} : Set G))) →
        ⁅S ⊓ Subgroup.centralizer ({b} : Set G), Subgroup.zpowers c⁆ ≠ ⊥ →
          Subgroup.zpowers b ∈ omegaA A

@[expose] noncomputable def Step1617 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Ctx169 G A c L → ∀ x ∈ Subgroup.normalizer (A : Set G), x ^ 3 = 1 → x ∈ A

@[expose] noncomputable def Step1618 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Ctx169 G A c L → ∀ g : G, g * c * g⁻¹ ∈ A →
      Subgroup.zpowers (g * c * g⁻¹) = Subgroup.zpowers c

@[expose] noncomputable def Step1618Trans : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Ctx169 G A c L → (∀ x ∈ Subgroup.normalizer (A : Set G), x ^ 3 = 1 → x ∈ A) →
    ∀ g : G, g ∉ Subgroup.normalizer (Subgroup.zpowers c : Set G) → g * c * g⁻¹ ∈ A →
      Nat.card (A ⊓ L.map (MulAut.conj g).toMonoidHom : Subgroup G) = 9 ∧
      ∀ y ∈ A ⊓ L.map (MulAut.conj g).toMonoidHom, y ≠ 1 →
        ∀ z ∈ A ⊓ L.map (MulAut.conj g).toMonoidHom, z ≠ 1 →
          ∃ w ∈ Subgroup.normalizer (A : Set G) ⊓ L.map (MulAut.conj g).toMonoidHom,
            w * y * w⁻¹ = z

@[expose] noncomputable def Step1619 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Ctx169 G A c L →
      IsEmpty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* projSL 3 (GaloisField 2 2)) ∧
        ∀ Y ∈ scriptY3 A (lB A), Group.IsSolvable ↥Y

section Data1619

variable {G : Type} [Group G] [Finite G]

structure Data1619 (A : Subgroup G) (c : G) (L : Subgroup G) (b : G) (n p : ℕ)
    (P : Subgroup G) : Prop where
  mem_A : b ∈ A
  mem_L : b ∈ L
  not_mem : b ∉ Subgroup.zpowers c
  isZ3 : IsZ3LThreeTwo A c L n
  prime : p.Prime
  three_lt : 3 < p
  dvd : (2 : ZMod p) ^ n = Sec15.sign1519 n p
  mem_Q : P ∈ scriptQPi A (lB A) (L ⊓ Subgroup.centralizer ({b} : Set G)) (piOf p)
  elem : CFSG.Assembly.IsElemAbelian p P
  card : Nat.card P = p ^ 2

end Data1619

@[expose] noncomputable def Para1619 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Ctx169 G A c L → ∀ n : ℕ, IsZ3LThreeTwo A c L n →
      IsEmpty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* projSL 3 (GaloisField 2 2)) →
      (∀ Y ∈ scriptY3 A (lB A), Group.IsSolvable ↥Y) →
      IsEmpty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* projSU 3 2 3) →
        ∃ (b : G) (p : ℕ) (P : Subgroup G), Data1619 A c L b n p P

@[expose] noncomputable def Step169U38 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Ctx169 G A c L → IsEmpty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* projSU 3 2 3)

@[expose] noncomputable def Step1620 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Ctx169 G A c L → ∀ (b : G) (n p : ℕ) (P : Subgroup G), Data1619 A c L b n p P →
      ∀ X ∈ collectionIn (scriptQ A (lB A)) P, X ≠ ⊥ → ∀ Y ∈ scriptY3 A (lB A), ¬ X ≤ Y

@[expose] noncomputable def Step1621 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Ctx169 G A c L → ∀ a ∈ A, a ≠ 1 →
      CFSG.Open.pCoreOf 2 (Subgroup.centralizer ({a} : Set G)) = ⊥

@[expose] noncomputable def Step1621Conj : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Ctx169 G A c L → ∀ (b : G) (n p : ℕ) (P : Subgroup G), Data1619 A c L b n p P →
      ∀ a ∈ A, a ≠ 1 → ∃ w ∈ Subgroup.normalizer (A : Set G),
        P.map (MulAut.conj w).toMonoidHom ≤ Subgroup.centralizer ({a} : Set G)

@[expose] noncomputable def Step1622 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Ctx169 G A c L → ∀ M : Subgroup G, c ∈ M → M ≠ ⊤ →
      ∀ P : Sylow 3 ↥(normalClosureSub M (Subgroup.zpowers c)),
        IsCyclic ↥(P : Subgroup ↥(normalClosureSub M (Subgroup.zpowers c)))

@[expose] noncomputable def Step1623 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Ctx169 G A c L → ∃ m : ℕ, 1 ≤ m ∧ Nonempty (↥L ≃* projSL 3 (GaloisField 2 m))

section Data1623

variable {G : Type} [Group G]

@[expose] def kPara1623 (L V : Subgroup G) : Subgroup G :=
  inSubgroup perfectResidual (L ⊓ Subgroup.normalizer (V : Set G))

structure Data1623 (L : Subgroup G) (b : G) (m p : ℕ) (P V X : Subgroup G) : Prop where
  le_L : V ≤ L
  elem : CFSG.Assembly.IsElemAbelian 2 V
  card : Nat.card V = 2 ^ (2 * m)
  le_P : X ≤ P
  card_X : Nat.card X = p
  mem_K : b ∈ kPara1623 L V
  le_K : X ≤ kPara1623 L V
  le_V : V ≤ kPara1623 L V
  quot : ∃ _ : (V.subgroupOf (kPara1623 L V)).Normal,
    Nonempty (↥(kPara1623 L V) ⧸ V.subgroupOf (kPara1623 L V) ≃* projSL 2 (GaloisField 2 m))

end Data1623

@[expose] noncomputable def Para1623 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Ctx169 G A c L → ∀ (b : G) (n p : ℕ) (P : Subgroup G), Data1619 A c L b n p P →
      ∀ m : ℕ, 1 ≤ m → Nonempty (↥L ≃* projSL 3 (GaloisField 2 m)) →
        ∃ V X : Subgroup G, Data1623 L b m p P V X

@[expose] noncomputable def Step1624 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Ctx169 G A c L → ∀ (b : G) (n p : ℕ) (P : Subgroup G), Data1619 A c L b n p P →
      ∀ (m : ℕ) (V X : Subgroup G), Data1623 L b m p P V X →
        ∃ d ∈ Subgroup.zpowers c ⊔ Subgroup.zpowers b, d ∉ Subgroup.zpowers c ∧
          ∃ U : Subgroup G, U ≤ Subgroup.centralizer ({d} : Set G) ∧ IsPGroup 2 U ∧
            U ≠ ⊥ ∧ U = ⁅U, X⁆

@[expose] noncomputable def Step169PComm : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Ctx169 G A c L → ∀ (b : G) (n p : ℕ) (P : Subgroup G), Data1619 A c L b n p P →
      P = ⁅P, A⁆

@[expose] noncomputable def Step169TwoBridge : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G)
    (h : Sec15R G A c L),
    Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* projSL 3 (GaloisField 2 2)) →
    Nonempty (lBarA c L A ≃* Multiplicative (ZMod 3) × Sec12.lBar c L) →
      letI := kerAO2_normal h.toSec13Data.le_normalizer
      Nonempty (↥(A ⊔ L) ⧸ kerAO2 A L ≃* Multiplicative (ZMod 3) × projSL 3 (GaloisField 2 2))

end CFSG.RankThree.PartTwo.Sec16
