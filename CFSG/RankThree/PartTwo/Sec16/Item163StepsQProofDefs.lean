module

public import CFSG.RankThree.PartTwo.Sec16.Item163Proof
public import CFSG.RankThree.PartTwo.Sec15.Item15More

public section

namespace CFSG.RankThree.PartTwo.Sec16

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec15
  CFSG.GH74.GLS

section Vocabulary

variable {G : Type} [Group G] [Finite G]

@[expose] def HasInvEven (A L : Subgroup G) : Prop :=
  ∃ K : Subgroup G, K ≤ L ∧ A ≤ Subgroup.normalizer (K : Set G) ∧ ¬ 3 ∣ Nat.card K ∧
    2 ∣ Nat.card K

end Vocabulary

@[expose] def Step163QLNE : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec15R G A c L → (∀ Y ∈ scriptY0Star A (lB A), L ≤ Y) → CFSG.Open.pCoreOf 2 L = ⊥ →
      ¬ IsL3TwoPow L → (scriptY0Star A (lB A)).Nonempty →
        ∃ Q ∈ scriptQPi A (lB A) L (piOf 2), Q ≠ ⊥

@[expose] def KS163QLInv : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec15R G A c L → ¬ IsL3TwoPow L →
    IsEmpty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* CFSG.Blueprint.NativeSporadic.J2) →
    IsEmpty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* CFSG.Blueprint.NativeSporadic.M12) →
    Odd (Nat.card (aschbacherSolvableCore 3 ↥L)) → HasInvEven A L

@[expose] def KS163QLInvL3 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec15R G A c L → ¬ IsL3TwoPow L → IsLThreePi (↥L ⧸ aschbacherSolvableCore 3 ↥L) →
    Odd (Nat.card (aschbacherSolvableCore 3 ↥L)) → HasInvEven A L

@[expose] def Step163TwoPowNE : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec15R G A c L → (∀ Y ∈ scriptY0Star A (lB A), L ≤ Y) → CFSG.Open.pCoreOf 2 L = ⊥ →
      IsL3TwoPow L → (scriptY0Star A (lB A)).Nonempty → ∃ R : Subgroup G, GoodR163 A L R

@[expose] noncomputable def Step163TwoPowShape : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec15R G A c L → CFSG.Open.pCoreOf 2 L = ⊥ → IsL3TwoPow L →
    ∀ Y ∈ scriptY0Star A (lB A), ∀ hYA : A ≤ Subgroup.normalizer (Y : Set G), L ≤ Y →
      Y = (Y ⊓ L) ⊔ CFSG.Open.pCoreOf 2 Y → omegaA A = {Subgroup.zpowers c} →
      Nonempty (lBarA c L A ≃* Multiplicative (ZMod 3) × Sec12.lBar c L) →
        IsSimpleGroup ↥L ∧ ∃ n : ℕ, 4 ≤ n ∧
          (letI := kerAO2_normal hYA
            ∃ T : Type, ∃ _ : Group T, Sec4.IsoLThreePi T 2 n ∧
              Nonempty (↥(A ⊔ Y) ⧸ kerAO2 A Y ≃* Multiplicative (ZMod 3) × T))

@[expose] def Step163VNE : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec15R G A c L → (∀ Y ∈ scriptY0Star A (lB A), L ≤ Y) → CFSG.Open.pCoreOf 2 L = ⊥ →
      ¬ IsL3TwoPow L → (scriptY0Star A (lB A)).Nonempty → ∃ R : Subgroup G, GoodR163 A L R

@[expose] def Step163VR : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec15R G A c L → (∀ Y ∈ scriptY0Star A (lB A), L ≤ Y) → CFSG.Open.pCoreOf 2 L = ⊥ →
      ¬ IsL3TwoPow L → ∀ Y ∈ scriptY0Star A (lB A),
        ∀ S ∈ scriptQPiStar A (lB A) (Subgroup.normalizer (Y : Set G)) (piOf 2),
          S ⊓ L ∈ scriptQPiStar A (lB A) L (piOf 2) → S ⊓ L ≠ ⊥ →
            ∃ R : Subgroup G, GoodR163 A L R

@[expose] def Step163L4A7 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec15R G A c L →
    Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* alternatingGroup (Fin 7)) →
    ∀ Y ∈ scriptY0Star A (lB A), L ≤ Y → ¬ Y ≤ L ⊔ CFSG.Open.pCoreOf 2 Y →
      L ∈ scriptY4 A (lB A)

@[expose] noncomputable def Step163DeltaY : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec15R G A c L → (∀ Y ∈ scriptY0Star A (lB A), L ≤ Y) → CFSG.Open.pCoreOf 2 L = ⊥ →
    ∀ Y ∈ scriptY0Star A (lB A), ∀ R : Subgroup G, GoodR163 A L R →
      R ≤ Subgroup.normalizer (Y : Set G) →
      CFSG.Open.pCoreOf 2 (R ⊔ L) ⊓ Subgroup.centralizer ({c} : Set G) = ⊥ →
        ∃ Y' ∈ scriptY3 A (lB A), oPrimeResidualOf 3 Y' ∈ scriptY4 A (lB A) ∧
          Y' = oPrimeResidualOf 3 Y' ⊔ CFSG.Open.pCoreOf 2 Y' ∧
          Y ∈ gam155 A (lB A) Y' (oPrimeResidualOf 3 Y') ∧
          (omg155 A (oPrimeResidualOf 3 Y') ∨
            Y = oPrimeResidualOf 3 Y' ⊔ CFSG.Open.pCoreOf 2 Y) ∧
          ∃ M ∈ CFSG.maximalTwoLocalsContaining ((A ⊔ Y' : Subgroup G) : Set G),
            Subgroup.normalizer (CFSG.Open.pCoreOf 2 (R ⊔ L) : Set G) ≤ M

@[expose] noncomputable def Step163DeltaQ : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec15R G A c L → (∀ Y ∈ scriptY0Star A (lB A), L ≤ Y) → CFSG.Open.pCoreOf 2 L = ⊥ →
    ∀ Y ∈ scriptY0Star A (lB A), ∀ R : Subgroup G, GoodR163 A L R →
      R ≤ Subgroup.normalizer (Y : Set G) →
      CFSG.Open.pCoreOf 2 (R ⊔ L) ⊓ Subgroup.centralizer ({c} : Set G) = ⊥ →
        CFSG.Open.pCoreOf 2 (R ⊔ L) ∈ scriptQ A (lB A)

@[expose] noncomputable def Step163XTransH : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec15R G A c L → (∀ Y ∈ scriptY0Star A (lB A), L ≤ Y) → CFSG.Open.pCoreOf 2 L = ⊥ →
      IsL3TwoPow L → (scriptY0Star A (lB A)).Nonempty → omegaA A = {Subgroup.zpowers c} →
        ∀ a : G, Subgroup.zpowers a ∈ omegaA A →
          TransOn A (lB A) (xA A) (Subgroup.centralizer ({a} : Set G))

@[expose] noncomputable def Step163XTransTwoPow : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec15R G A c L → (∀ Y ∈ scriptY0Star A (lB A), L ≤ Y) → CFSG.Open.pCoreOf 2 L = ⊥ →
      IsL3TwoPow L → (scriptY0Star A (lB A)).Nonempty → TransOn A (lB A) (xA A) ⊤

end CFSG.RankThree.PartTwo.Sec16
