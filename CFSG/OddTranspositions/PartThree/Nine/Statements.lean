module

public import CFSG.OddTranspositions.PartThree.Statements
public import CFSG.Quasithin.Background.A1cTransfer
public import
  CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionCosetNormalizerIndexCosetAction

public section

namespace CFSG.OddTranspositions.PartThree.Nine

open CFSG.Timmesfeld.Bridge.Asc72 CFSG.Timmesfeld.Connectivity
open CFSG.ProperTwoGeneratedCore.LocalCriterionCosetNormalizerIndex (cosetNormalizerPerm)
open scoped MatrixGroups

structure Th91Hyp {G : Type} [Group G] [Finite G] (D : Set G) (hC : HypothesisC D) : Prop where
  solv : ∀ N : Subgroup G, N.Normal → Group.IsSolvable N → N = ⊥
  rad : CFSG.solvableRadical (Halpha D hC.alpha) = Subgroup.center (Halpha D hC.alpha)
  bender : CFSG.BenderSuzuki.IsBenderGroup
    (Halpha D hC.alpha ⧸ Subgroup.center (Halpha D hC.alpha))

@[expose] def Th91Below (n : ℕ) : Prop :=
  ∀ (G : Type) [Group G] [Finite G], Nat.card G < n →
    ∀ (D : Set G) (hC : HypothesisC D), Th91Hyp D hC →
      ∃ f : ℕ, 2 ≤ f ∧
        Nonempty (Halpha D hC.alpha ⧸ Subgroup.center (Halpha D hC.alpha) ≃*
          CFSG.Theory.Comparator.PSL2Model f) ∧
        (Nonempty (G ≃* L2Wreath f 2) ∨
          (Nonempty (↥(commutator G) ≃* CFSG.Theory.Comparator.PSL2Model (2 * f)) ∧
            (commutator G).index = 2))

@[expose] def Lemma9_2Wreath : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (D : Set G) (hC : HypothesisC D), Th91Hyp D hC →
    (∃ M : Subgroup G, CFSG.Timmesfeld.Bridge.Asc72.IsMinimalNormal M ∧ ¬ IsSimpleGroup M) →
      ∃ f : ℕ, 2 ≤ f ∧
        Nonempty (Halpha D hC.alpha ⧸ Subgroup.center (Halpha D hC.alpha) ≃*
          CFSG.Theory.Comparator.PSL2Model f) ∧
        (Nonempty (G ≃* L2Wreath f 2) ∨
          (Nonempty (↥(commutator G) ≃* CFSG.Theory.Comparator.PSL2Model (2 * f)) ∧
            (commutator G).index = 2))

@[expose] def Lemma9_2 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (D : Set G) (hC : HypothesisC D), Th91Hyp D hC →
    (∀ M : Subgroup G, CFSG.Timmesfeld.Bridge.Asc72.IsMinimalNormal M → IsSimpleGroup M) →
      IsSimpleGroup (commutator G)

@[expose] def Conclusion9_3 {G : Type} [Group G] [Finite G] (D : Set G) (hC : HypothesisC D) :
    Prop :=
  hC.alpha = {hC.d} ∧
    (CFSG.pCore 2 (Halpha D hC.alpha)).map (Halpha D hC.alpha).subtype =
      Subgroup.zpowers hC.d ∧
    Subgroup.zpowers hC.d ⊔ CFSG.Quasithin.pResidualOf 2 (Halpha D hC.alpha) =
      Halpha D hC.alpha ∧
    Disjoint (Subgroup.zpowers hC.d) (CFSG.Quasithin.pResidualOf 2 (Halpha D hC.alpha))

@[expose] def Lemma9_3 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (D : Set G) (hC : HypothesisC D), Th91Hyp D hC →
    IsSimpleGroup (commutator G) → Conclusion9_3 D hC

@[expose] def Conclusion9_4 {G : Type} [Group G] [Finite G] (D : Set G) (hC : HypothesisC D)
    (T : Sylow 2 (Halpha D hC.alpha)) (S : Sylow 2 G) : Prop :=
  (S : Set G) ∩ D =
      ((T : Subgroup (Halpha D hC.alpha)).map (Halpha D hC.alpha).subtype : Set G) ∩ D ∧
    (S : Subgroup G) ≤ Subgroup.normalizer ((S : Set G) ∩ D) ∧
    (∀ a ∈ (S : Set G) ∩ D, ∀ b ∈ (S : Set G) ∩ D, ∀ c ∈ (S : Set G) ∩ D,
      ∀ e ∈ (S : Set G) ∩ D, a ≠ b → c ≠ e →
        ∃ g ∈ Subgroup.normalizer ((S : Set G) ∩ D), g * a * g⁻¹ = c ∧ g * b * g⁻¹ = e) ∧
    (Group.IsSolvable (cosetNormalizerPerm ((S : Set G) ∩ D)).range ∨
      (((S : Set G) ∩ D).ncard = 8 ∧
        Nonempty ((cosetNormalizerPerm ((S : Set G) ∩ D)).range ≃* PSL(2, ZMod 7))))

@[expose] def Lemma9_4 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (D : Set G) (hC : HypothesisC D), Th91Hyp D hC →
    IsSimpleGroup (commutator G) → Conclusion9_3 D hC →
    ∀ (T : Sylow 2 (Halpha D hC.alpha)) (S : Sylow 2 G),
      (T : Subgroup (Halpha D hC.alpha)).map (Halpha D hC.alpha).subtype ≤ S →
      Conclusion9_4 D hC T S

@[expose] def Conclusion9_5 {G : Type} [Group G] [Finite G] (D : Set G) (hC : HypothesisC D)
    (T : Sylow 2 (Halpha D hC.alpha)) (S : Sylow 2 G) : Prop :=
  Subgroup.centralizer ((S : Set G) ∩ D) =
      (T : Subgroup (Halpha D hC.alpha)).map (Halpha D hC.alpha).subtype ∧
    ¬ ∃ n : ℕ, Nonempty (Halpha D hC.alpha ⧸ Subgroup.center (Halpha D hC.alpha) ≃*
      CFSG.Theory.Comparator.PSU3Model n)

@[expose] def Lemma9_5 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (D : Set G) (hC : HypothesisC D), Th91Hyp D hC →
    IsSimpleGroup (commutator G) → Th91Below (Nat.card G) → Conclusion9_3 D hC →
    ∀ (T : Sylow 2 (Halpha D hC.alpha)) (S : Sylow 2 G),
      (T : Subgroup (Halpha D hC.alpha)).map (Halpha D hC.alpha).subtype ≤ S →
      Conclusion9_4 D hC T S → Conclusion9_5 D hC T S

@[expose] def Lemma9_6 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (D : Set G) (hC : HypothesisC D), Th91Hyp D hC →
    IsSimpleGroup (commutator G) → Th91Below (Nat.card G) → Conclusion9_3 D hC →
    ∀ (T : Sylow 2 (Halpha D hC.alpha)) (S : Sylow 2 G),
      (T : Subgroup (Halpha D hC.alpha)).map (Halpha D hC.alpha).subtype ≤ S →
      Conclusion9_4 D hC T S → Conclusion9_5 D hC T S →
      ¬ (((S : Set G) ∩ D).ncard = 8 ∧
        Nonempty ((cosetNormalizerPerm ((S : Set G) ∩ D)).range ≃* PSL(2, ZMod 7)))

@[expose] def IsRegularCore {G : Type} [Group G] (Δ : Set G) (Q : Subgroup G) : Prop :=
  Q ≤ Subgroup.normalizer Δ ∧
    (∀ n ∈ Subgroup.normalizer Δ, ∀ x ∈ Q, n * x * n⁻¹ ∈ Q) ∧
    IsPGroup 2 Q ∧ Subgroup.centralizer Δ ≤ Q ∧
    (∀ a ∈ Δ, ∀ b ∈ Δ, ∃ x ∈ Q, x * a * x⁻¹ = b) ∧
    ∀ x ∈ Q, ∀ a ∈ Δ, x * a * x⁻¹ = a → x ∈ Subgroup.centralizer Δ

@[expose] def Lemma9_6Q : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (D : Set G) (hC : HypothesisC D), Th91Hyp D hC →
    IsSimpleGroup (commutator G) → Conclusion9_3 D hC →
    ∀ (T : Sylow 2 (Halpha D hC.alpha)) (S : Sylow 2 G),
      (T : Subgroup (Halpha D hC.alpha)).map (Halpha D hC.alpha).subtype ≤ S →
      Conclusion9_4 D hC T S → Conclusion9_5 D hC T S →
      Group.IsSolvable (cosetNormalizerPerm ((S : Set G) ∩ D)).range →
      ∃ Q : Subgroup G, IsRegularCore ((S : Set G) ∩ D) Q

@[expose] def Lemma9_7 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (D : Set G) (hC : HypothesisC D), Th91Hyp D hC →
    IsSimpleGroup (commutator G) → Th91Below (Nat.card G) → Conclusion9_3 D hC →
    ∀ (T : Sylow 2 (Halpha D hC.alpha)) (S : Sylow 2 G),
      (T : Subgroup (Halpha D hC.alpha)).map (Halpha D hC.alpha).subtype ≤ S →
      Conclusion9_4 D hC T S → Conclusion9_5 D hC T S →
      ∀ Q : Subgroup G, IsRegularCore ((S : Set G) ∩ D) Q →
        ∀ d ∈ D, ∀ e ∈ D, d ≠ e → Commute d e →
          d * e ∈ Subgroup.normalizer ((S : Set G) ∩ D) → d * e ∈ Q

@[expose] def Final9_1 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (D : Set G) (hC : HypothesisC D), Th91Hyp D hC →
    IsSimpleGroup (commutator G) → Th91Below (Nat.card G) → Conclusion9_3 D hC →
    ∀ (T : Sylow 2 (Halpha D hC.alpha)) (S : Sylow 2 G),
      (T : Subgroup (Halpha D hC.alpha)).map (Halpha D hC.alpha).subtype ≤ S →
      Conclusion9_4 D hC T S → Conclusion9_5 D hC T S →
      ∀ Q : Subgroup G, IsRegularCore ((S : Set G) ∩ D) Q →
        (∀ d ∈ D, ∀ e ∈ D, d ≠ e → Commute d e →
          d * e ∈ Subgroup.normalizer ((S : Set G) ∩ D) → d * e ∈ Q) →
        ∃ f : ℕ, 2 ≤ f ∧
          Nonempty (Halpha D hC.alpha ⧸ Subgroup.center (Halpha D hC.alpha) ≃*
            CFSG.Theory.Comparator.PSL2Model f) ∧
          (Nonempty (G ≃* L2Wreath f 2) ∨
            (Nonempty (↥(commutator G) ≃* CFSG.Theory.Comparator.PSL2Model (2 * f)) ∧
              (commutator G).index = 2))

end CFSG.OddTranspositions.PartThree.Nine
