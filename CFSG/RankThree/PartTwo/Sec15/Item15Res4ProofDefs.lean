module

public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.RankThree.PartTwo.Sec15.HypR
public import CFSG.RankThree.PartTwo.Sec15.Item15Statements

public section

namespace CFSG.RankThree.PartTwo.Sec15

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank CFSG.GH74.GLS

structure Conf1515HJ {G : Type} [Group G] [Finite G] (A : Subgroup G) (c : G) (L Y : Subgroup G) :
    Prop where
  sec15R : Sec15R G A c L
  j2 : Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* CFSG.Blueprint.NativeSporadic.J2)
  mem_scriptY0Star : Y ∈ scriptY0Star A (lB A)
  meetsY4 : MeetsY4 A (lB A) L Y
  eq_Y : Y = (Y ⊓ L) ⊔ CFSG.Open.pCoreOf 2 Y
  eq_L : L = (L ⊓ Y) ⊔ CFSG.Open.pCoreOf 2 L
  omega_ne : omegaA A ≠ {Subgroup.zpowers c}

@[expose] def IsZCentral {G : Type} [Group G] (L : Subgroup G) (d : G) : Prop :=
  ∃ S : Subgroup G, CFSG.ABGLocalTools.IsSylowOf 3 S L ∧
    (Subgroup.center S).map S.subtype = Subgroup.zpowers d

@[expose] noncomputable def Step1515HJTrans : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec15R G A c L →
    Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* CFSG.Blueprint.NativeSporadic.J2) →
    omegaA A ≠ {Subgroup.zpowers c} →
    ∀ d ∈ A, d ≠ 1 → IsZCentral L d →
    ∀ a ∈ Subgroup.closure {c, d}, a ∉ Subgroup.zpowers d →
      ∃ w ∈ Subgroup.normalizer (A : Set G),
        w ∈ Subgroup.normalizer (Subgroup.zpowers d : Set G) ∧
          (Subgroup.zpowers c).map (MulAut.conj w).toMonoidHom = Subgroup.zpowers a

@[expose] noncomputable def Step1515HJConj : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L Y : Subgroup G),
    Conf1515HJ A c L Y → ∀ d ∈ A, d ≠ 1 → IsZCentral L d →
    ∀ w ∈ Subgroup.normalizer (A : Set G),
      w ∈ Subgroup.normalizer (Subgroup.zpowers d : Set G) →
      w * c * w⁻¹ ∈ Subgroup.closure {c, d} → w * c * w⁻¹ ∉ Subgroup.zpowers c →
      ⁅CFSG.Open.pCoreOf 2 Y ⊓ Subgroup.centralizer ({w * c * w⁻¹} : Set G),
          Subgroup.zpowers d⁆ ≠ ⊥ →
        Y.map (MulAut.conj w).toMonoidHom = Y

@[expose] noncomputable def Step1515HJQN : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L Y : Subgroup G),
    Conf1515HJ A c L Y → ∀ d ∈ A, d ≠ 1 → IsZCentral L d →
    ¬ Odd (Nat.card ↥(Subgroup.normalizer (Y : Set G) ⊓
      pPrimeCoreOf 3 (Subgroup.centralizer ({d} : Set G)))) →
      ∃ Q ∈ scriptQPiStar A (lB A) (pPrimeCoreOf 3 (Subgroup.centralizer ({d} : Set G)))
          (piOf 2),
        Subgroup.normalizer (A : Set G) ⊓ Subgroup.normalizer (Q : Set G) ⊓
            Subgroup.normalizer (Subgroup.closure ({c, d} : Set G) : Set G) ≤
          Subgroup.normalizer (Y : Set G)

@[expose] noncomputable def Step1515HJVFour : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L Y : Subgroup G),
    Conf1515HJ A c L Y → ∀ d ∈ A, d ≠ 1 → IsZCentral L d →
    ⁅CFSG.Open.pCoreOf 2 Y, Subgroup.zpowers c⁆ ≤ Subgroup.centralizer ({d} : Set G) →
    Odd (Nat.card ↥(Subgroup.normalizer (Y : Set G) ⊓
      pPrimeCoreOf 3 (Subgroup.centralizer ({d} : Set G)))) →
    ⁅CFSG.Open.pCoreOf 2 Y, Subgroup.zpowers c⁆ ≠ ⊥ →
      Nat.card ↥⁅CFSG.Open.pCoreOf 2 Y, Subgroup.zpowers c⁆ = 4

@[expose] noncomputable def Step1515HJVR : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L Y : Subgroup G),
    Conf1515HJ A c L Y → ∀ d ∈ A, d ≠ 1 → IsZCentral L d →
    ⁅CFSG.Open.pCoreOf 2 Y, Subgroup.zpowers c⁆ ≤ Subgroup.centralizer ({d} : Set G) →
    Odd (Nat.card ↥(Subgroup.normalizer (Y : Set G) ⊓
      pPrimeCoreOf 3 (Subgroup.centralizer ({d} : Set G)))) →
    Nat.card ↥⁅CFSG.Open.pCoreOf 2 Y, Subgroup.zpowers c⁆ = 4 →
      ⁅CFSG.Open.pCoreOf 2 (Subgroup.normalizer (Y : Set G)), Subgroup.zpowers c⁆ ≤
        ⁅CFSG.Open.pCoreOf 2 Y, Subgroup.zpowers c⁆

@[expose] noncomputable def Step1515HJVBlock : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L Y : Subgroup G),
    Conf1515HJ A c L Y → ∀ d ∈ A, d ≠ 1 → IsZCentral L d →
    ⁅CFSG.Open.pCoreOf 2 Y, Subgroup.zpowers c⁆ ≤ Subgroup.centralizer ({d} : Set G) →
    Odd (Nat.card ↥(Subgroup.normalizer (Y : Set G) ⊓
      pPrimeCoreOf 3 (Subgroup.centralizer ({d} : Set G)))) →
    Nat.card ↥⁅CFSG.Open.pCoreOf 2 Y, Subgroup.zpowers c⁆ = 4 →
    ⁅CFSG.Open.pCoreOf 2 (Subgroup.normalizer (Y : Set G)), Subgroup.zpowers c⁆ =
      ⁅CFSG.Open.pCoreOf 2 Y, Subgroup.zpowers c⁆ → False

@[expose] noncomputable def Step1515HJEndX : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L Y : Subgroup G),
    Conf1515HJ A c L Y → ∀ d ∈ A, d ≠ 1 → IsZCentral L d →
    Odd (Nat.card ↥(Subgroup.normalizer (Y : Set G) ⊓
      pPrimeCoreOf 3 (Subgroup.centralizer ({d} : Set G)))) →
    Y ≤ Subgroup.centralizer ({c} : Set G) →
      deltaZero A (lB A) (Subgroup.centralizer ({d} : Set G)) =
        inSubgroup perfectResidual (L ⊓ Subgroup.centralizer ({d} : Set G)) ⊔
          pPrimeCoreOf 3 (deltaZero A (lB A) (Subgroup.centralizer ({d} : Set G)))

@[expose] noncomputable def Step1515HJEndT0 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L Y : Subgroup G),
    Conf1515HJ A c L Y → ∀ d ∈ A, d ≠ 1 → IsZCentral L d →
    Odd (Nat.card ↥(Subgroup.normalizer (Y : Set G) ⊓
      pPrimeCoreOf 3 (Subgroup.centralizer ({d} : Set G)))) →
    Y ≤ Subgroup.centralizer ({c} : Set G) →
    deltaZero A (lB A) (Subgroup.centralizer ({d} : Set G)) =
      inSubgroup perfectResidual (L ⊓ Subgroup.centralizer ({d} : Set G)) ⊔
        pPrimeCoreOf 3 (deltaZero A (lB A) (Subgroup.centralizer ({d} : Set G))) → False

@[expose] noncomputable def Step158CartanP : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec15R G A c L → ∀ (p e : ℕ) [Fact p.Prime], 1 ≤ e →
    Sec4.IsoLThreePi (↥L ⧸ aschbacherSolvableCore 3 ↥L) p e →
    ∀ Y ∈ scriptY0 A (lB A), MeetsY4 A (lB A) L Y →
    ∀ P : Subgroup G, A ≤ P →
      CFSG.ABGLocalTools.IsSylowOf 3 P
        (Subgroup.normalizer (Subgroup.zpowers c : Set G) ⊓ Subgroup.normalizer (Y : Set G)) →
      A ≠ omegaOneThree P → ∃ E F : Subgroup G, E ≤ P ∧ F ≤ P ∧
        CFSG.Assembly.IsElemAbelian 3 E ∧ Nat.card E = 27 ∧
        Late.sectionCentralizer E L ((aschbacherSolvableCore 3 L).map L.subtype) =
          (Subgroup.zpowers c : Set G) ∧
        Sec4.IsTypeCOn E L ∧
        CFSG.Assembly.IsElemAbelian 3 F ∧ Nat.card F = 27 ∧ F ≤ Subgroup.zpowers c ⊔ L ∧
        Nat.card (F ⊓ L : Subgroup G) = 9 ∧
        (∀ y ∈ F ⊓ L, y ≠ 1 → ∀ z ∈ F ⊓ L, z ≠ 1 → ∃ l ∈ L, l * y * l⁻¹ = z) ∧
        F ≤ Subgroup.normalizer (E : Set G)

end CFSG.RankThree.PartTwo.Sec15
