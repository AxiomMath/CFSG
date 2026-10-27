module

public import CFSG.RankThree.PartTwo.Sec15.Item15Statements
public import CFSG.Foundations.HigherElementaryThompson

public section

namespace CFSG.RankThree.PartTwo.Sec15

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank CFSG.GH74.GLS

@[expose] def Item3_15 : Prop :=
  ∀ (X : Type) [Group X] [Finite X], generalizedFitting X = CFSG.pCore 2 X →
    ((∃ n : ℕ, 1 ≤ n ∧ Even n ∧ Nonempty (oResidual 2 (X ⧸ CFSG.pCore 2 X) ≃*
          CFSG.Assembly.RankThreeEven.projSL 2 (GaloisField 2 n))) ∨
      Sec4.IsTripleCover (oResidual 2 (X ⧸ CFSG.pCore 2 X)) (alternatingGroup (Fin 6)) ∨
      Nonempty (oResidual 2 (X ⧸ CFSG.pCore 2 X) ≃* alternatingGroup (Fin 7))) →
    ∀ A : Subgroup X, CFSG.Assembly.IsElemAbelian 3 A →
      (∀ B : Subgroup X, CFSG.Assembly.IsElemAbelian 3 B → A ≤ B → B = A) →
      ∀ S ∈ maxInvariantPiSubgroups ⊤ A (piOf 2),
        (∃ C : Subgroup X, C ≠ ⊥ ∧ C ≤ S ∧ (C.subgroupOf S).Characteristic ∧ C.Normal) ∨
          IsScriptLBlock ⊤ (oResidual 2 X)

@[expose] def Item3_22One : Prop :=
  ∀ (X : Type) [Group X] [Finite X], generalizedFitting X = CFSG.pCore 2 X →
    Nonempty (X ⧸ CFSG.pCore 2 X ≃* CFSG.Blueprint.NativeSporadic.J2) →
    ∀ R : Subgroup X, CFSG.pCore 2 X ≤ R →
      Nonempty (R.map (QuotientGroup.mk' (CFSG.pCore 2 X)) ≃*
        Multiplicative (ZMod 2) × Multiplicative (ZMod 2)) →
      Nonempty (Subgroup.centralizer
          ((R.map (QuotientGroup.mk' (CFSG.pCore 2 X)) : Subgroup (X ⧸ CFSG.pCore 2 X)) :
            Set (X ⧸ CFSG.pCore 2 X)) ≃*
        (Multiplicative (ZMod 2) × Multiplicative (ZMod 2)) × alternatingGroup (Fin 5)) →
      ((omegaOneCenter (⊤ : Subgroup R)).map R.subtype).Normal ∧
            ((higherElemThompson R 0).map R.subtype).Normal ∨
          ((omegaOneCenter (⊤ : Subgroup R)).map R.subtype).Normal ∧
            ((higherElemThompsonOmega R 2).map R.subtype).Normal ∨
          ((higherElemThompson R 0).map R.subtype).Normal ∧
            ((higherElemThompsonOmega R 2).map R.subtype).Normal

@[expose] def Item3_22Two : Prop :=
  ∀ (X : Type) [Group X] [Finite X], generalizedFitting X = CFSG.pCore 2 X →
    Nonempty (X ⧸ CFSG.pCore 2 X ≃* CFSG.Blueprint.NativeSporadic.J2) →
    ∀ R : Subgroup X, CFSG.pCore 2 X ≤ R →
      Nonempty (R.map (QuotientGroup.mk' (CFSG.pCore 2 X)) ≃*
        Multiplicative (ZMod 2) × Multiplicative (ZMod 2)) →
      Nonempty (Subgroup.centralizer
          ((R.map (QuotientGroup.mk' (CFSG.pCore 2 X)) : Subgroup (X ⧸ CFSG.pCore 2 X)) :
            Set (X ⧸ CFSG.pCore 2 X)) ≃*
        (Multiplicative (ZMod 2) × Multiplicative (ZMod 2)) × alternatingGroup (Fin 5)) →
      ¬ (omegaOneCenter (⊤ : Subgroup R)).map R.subtype ≤ Subgroup.center X →
        ((higherElemThompson R 0).map R.subtype).Normal ∧
          ((higherElemThompson R 1).map R.subtype).Normal

@[expose] def Item3_22 : Prop :=
  Item3_22One ∧ Item3_22Two

theorem item3_22_iff : Item3_22 ↔ Item3_22One ∧ Item3_22Two :=
  Iff.rfl

variable {G : Type} [Group G] [Finite G]

@[expose] def normalClosureSub (X E : Subgroup G) : Subgroup G :=
  (Subgroup.normalClosure ((E.subgroupOf X : Subgroup X) : Set X)).map X.subtype

@[expose] def Item14_23 (A L : Subgroup G) : Prop :=
  ∀ p : ℕ, p.Prime → 3 < p → ∀ E : Subgroup G, E ≠ ⊥ → CFSG.Assembly.IsElemAbelian p E →
    E = ⁅E, A⁆ → E ≤ L → ∀ X ∈ invariantPiSubgroups ⊤ A (piCompl 3), E ≤ X →
      Group.IsSolvable ↥(normalClosureSub X E)

@[expose] noncomputable def Item14_24 (A : Subgroup G) (LB : Subgroup G → Subgroup G) (c : G)
    (L : Subgroup G) : Prop :=
  ∀ Y ∈ scriptY3 A LB, ∀ (hYA : A ≤ Subgroup.normalizer (Y : Set G)) (n : ℕ), 4 ≤ n →
    (letI := kerAO2_normal hYA
      ∃ T : Type, ∃ _ : Group T, Sec4.IsoLThreePi T 2 n ∧
        Nonempty (↥(A ⊔ Y) ⧸ kerAO2 A Y ≃* Multiplicative (ZMod 3) × T)) →
    Y = (Y ⊓ L) ⊔ CFSG.Open.pCoreOf 2 Y → generalizedFitting ↥Y = CFSG.pCore 2 ↥Y →
    IsSimpleGroup ↥L → omegaA A = {Subgroup.zpowers c} →
      ∃ a ∈ A, a ∉ Subgroup.zpowers c ∧
        CFSG.Open.pCoreOf 2 Y ⊓
            CFSG.Open.pCoreOf 2 (delta A LB (Subgroup.centralizer ({a} : Set G))) ≠ ⊥

end CFSG.RankThree.PartTwo.Sec15
