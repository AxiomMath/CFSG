module

public import CFSG.RankThree.PartTwo.Sec16.Notation
public import CFSG.RankThree.PartTwo.Sec14.Item1411Chain
public import CFSG.RankThree.PartTwo.Sec13.Steps

public section

namespace CFSG.RankThree.PartTwo.Sec16

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec15 CFSG.RankThree.PartTwo.Late
  CFSG.RankThree.LocalRank CFSG.GH74.GLS

variable {G : Type} [Group G] [Finite G]

@[expose] def IsTwoNilpotent (X : Type*) [Group X] : Prop :=
  ∃ (N : Subgroup X) (_ : N.Normal), Odd (Nat.card N) ∧ IsPGroup 2 (X ⧸ N)

@[expose] def Item162 (A : Subgroup G) (LB : Subgroup G → Subgroup G) : Prop :=
  ∀ Y₁ ∈ scriptY0Star A LB, ∀ Y₂ ∈ scriptY0Star A LB,
    (∃ Q ∈ scriptQPi A LB
        (Subgroup.normalizer (Y₁ : Set G) ⊓ Subgroup.normalizer (Y₂ : Set G)) (piOf 2),
      Q ≠ ⊥) →
      ∃ x ∈ xA A, Y₁ = Y₂.map (MulAut.conj x).toMonoidHom

@[expose] def Item163 (A : Subgroup G) (LB : Subgroup G → Subgroup G) (c : G)
    (L : Subgroup G) : Prop :=
  ∀ Y ∈ scriptY0Star A LB,
    Subgroup.normalizer (A : Set G) ≤ Subgroup.normalizer (Y : Set G) ∧
      (∀ S ∈ scriptQPiStar A LB ⊤ (piOf 2), S ≤ Subgroup.normalizer (Y : Set G)) ∧
      scriptY0Star A LB = {Y} ∧ L ≤ Y ∧
      (Nonempty (↥Y ⧸ CFSG.pCore 2 ↥Y ≃* alternatingGroup (Fin 10)) ∨
        omegaA A = {Subgroup.zpowers c})

@[expose] def Item164 (A : Subgroup G) (LB : Subgroup G → Subgroup G) (c : G) : Prop :=
  ∀ Y ∈ scriptY0Star A LB,
    Subgroup.normalizer (Subgroup.zpowers c : Set G) ≤ Subgroup.normalizer (Y : Set G)

@[expose] def Item165 (A : Subgroup G) (LB : Subgroup G → Subgroup G) (L : Subgroup G) : Prop :=
  (∃ n : ℕ, 1 ≤ n ∧ Sec4.IsoLThreePi (↥L ⧸ aschbacherSolvableCore 3 ↥L) 2 n) →
    ∀ Y ∈ scriptY0Star A LB, ∀ Z ∈ scriptY3 A LB, Z ≤ Subgroup.normalizer (Y : Set G)

@[expose] noncomputable def Item166 (A : Subgroup G) (LB : Subgroup G → Subgroup G) : Prop :=
  ∀ Y ∈ scriptY0Star A LB,
    (∀ X ∈ scriptY A, X = delta A LB X → ∀ K ∈ thetaComponentsIn X,
      (∃ n : ℕ, CFSG.Blueprint.SuzukiModel (↥K ⧸ aschbacherSolvableCore 3 ↥K) 2 n) →
        CFSG.pCore 2 ↥K = aschbacherSolvableCore 3 ↥K ∧
          (K : Set G) ⊆ sectionCentralizer (Subgroup.normalizer (Y : Set G)) Y
            (CFSG.Open.pCoreOf 2 Y)) ∧
      ∀ X ∈ scriptY3 A LB, ¬ Group.IsSolvable ↥X → X ≤ Subgroup.normalizer (Y : Set G)

@[expose] noncomputable def Item167 (A : Subgroup G) (LB : Subgroup G → Subgroup G) (c : G)
    (L : Subgroup G) : Prop :=
  ∀ Y ∈ scriptY1Star A LB,
    generalizedFitting ↥(deltaZero A LB Y) = CFSG.pCore 2 ↥(deltaZero A LB Y) ∧
      generalizedFitting (↥(deltaZero A LB Y) ⧸ CFSG.pCore 2 ↥(deltaZero A LB Y)) =
        oResidual 2 (↥(deltaZero A LB Y) ⧸ CFSG.pCore 2 ↥(deltaZero A LB Y)) ∧
      (Y ∈ scriptY3Star A LB → Group.IsSolvable ↥Y → deltaZero A LB Y ≠ ⊥ →
        ((scriptY0 A LB) = ∅ →
          ∃ n : ℕ, 2 < n ∧ Sec4.IsoLThreePi (↥L ⧸ aschbacherSolvableCore 3 ↥L) 2 n ∧
            Nonempty (lBarA c L A ≃* Multiplicative (ZMod 3) × Sec12.lBar c L)) →
        IsTwoNilpotent (↥Y ⧸ CFSG.pCore 2 ↥Y) ∧
          (generalizedFitting ↥Y = CFSG.pCore 2 ↥Y ∨
            (scriptY0 A LB = ∅ ∧
              generalizedFitting ↥Y = CFSG.pCore 2 ↥Y ⊔ Subgroup.center ↥Y)))

@[expose] noncomputable def Item169 (A : Subgroup G) (LB : Subgroup G → Subgroup G)
    (L : Subgroup G) : Prop :=
  (scriptY0 A LB).Nonempty ∧
    IsEmpty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃*
      CFSG.Assembly.RankThreeEven.projSL 3 (GaloisField 2 2))

end CFSG.RankThree.PartTwo.Sec16
