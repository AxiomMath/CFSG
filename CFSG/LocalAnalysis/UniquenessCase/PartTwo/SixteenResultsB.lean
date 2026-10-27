module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenDefsB
public import CFSG.Quasithin.Background.C2Blocks

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

@[expose] def R16_25 (D : Data G) : Prop :=
  ∀ (V₀ V L : Subgroup G) (hV : IsElemAbelian 2 V), Sect16 D V₀ V L hV →
    ¬ Case167_8 D V₀ V hV L

@[expose] def R16_26 (D : Data G) : Prop :=
  ∀ (V₀ V L : Subgroup G) (hV : IsElemAbelian 2 V), Sect16 D V₀ V L hV →
    Case167_8 D V₀ V hV L →
      (∃ Q : Vtil V₀ V hV → ZMod 2, IsPlusQuadF2 Q ∧ QuadInvariant Q (lBar V₀ V hV L)) ∧
      ∀ Q : Vtil V₀ V hV → ZMod 2, IsPlusQuadF2 Q → QuadInvariant Q (lBar V₀ V hV L) →
        (∀ w : Vtil V₀ V hV, w ≠ 1 → Q w = 0 → IsE64L3 ↥(ptCent (Mbar D.M V₀ V hV) w)) ∧
        ∀ w : Vtil V₀ V hV, Q w ≠ 0 →
          CFSG.Quasithin.IsG2Two ↥(ptCent (Mbar D.M V₀ V hV) w) ∧
            ∀ x : IntMod V hV, mkTil V₀ V hV x = w → centralizer ({x.val} : Set G) ≤ D.M

@[expose] def R16_28 (D : Data G) : Prop :=
  ∀ (V₀ V L : Subgroup G) (hV : IsElemAbelian 2 V), Sect16 D V₀ V L hV →
    Case167_8 D V₀ V hV L →
      ((mSub V₀ + 4 : ℕ) : ℕ∞) ≤ rMV D.M V ∧ 1 < deltaInf D.M V

@[expose] def R16_29 (D : Data G) : Prop :=
  ∀ (V₀ V L : Subgroup G) (hV : IsElemAbelian 2 V), Sect16 D V₀ V L hV →
    Case167_8 D V₀ V hV L →
      E3.wClos V 0 D.T ≤ centralizer (V : Set G) ∧
        normalizer (E3.wClos V 0 D.T : Set G) ≤ D.M

@[expose] def R16_30 (D : Data G) : Prop :=
  ∀ (V₀ V L : Subgroup G) (hV : IsElemAbelian 2 V), Sect16 D V₀ V L hV →
    Case167_8 D V₀ V hV L → calO 1 D.M V₀ V = ∅

@[expose] def R16_31 (D : Data G) : Prop :=
  ∀ (V₀ V L : Subgroup G) (hV : IsElemAbelian 2 V), Sect16 D V₀ V L hV →
    Case167_8 D V₀ V hV L →
      V₀ = ⊥ ∧ ¬ centralizer (E3.cClos V 1 D.T : Set G) ≤ D.M

@[expose] def R16_32 (D : Data G) : Prop :=
  ∀ (V₀ V L : Subgroup G) (hV : IsElemAbelian 2 V), Sect16 D V₀ V L hV →
    Case167_8 D V₀ V hV L → ⁅E3.wClos V 1 D.T, V⁆ = ⊥

@[expose] def R16_33 (D : Data G) : Prop :=
  ∀ (V₀ V L : Subgroup G) (hV : IsElemAbelian 2 V), Sect16 D V₀ V L hV →
    ¬ Case167_5 D V₀ V hV L ∧ ¬ Case167_6 D V₀ V hV L

@[expose] def R16_38 (D : Data G) : Prop :=
  ∀ (V₀ V L : Subgroup G) (hV : IsElemAbelian 2 V), Sect16 D V₀ V L hV → ∀ m : ℕ,
    Case1633 D V₀ V hV L m → ∀ i : ℕ, i + 1 < m → calOStar (m + i) D.M V₀ V = ∅

@[expose] def R16_39 (D : Data G) : Prop :=
  ∀ (V₀ V L : Subgroup G) (hV : IsElemAbelian 2 V), Sect16 D V₀ V L hV → ∀ m : ℕ,
    Case1633 D V₀ V hV L m →
      m = 2 ∧ V₀ = ⊥ ∧ ¬ centralizer (E3.cClos V 2 D.T : Set G) ≤ D.M

@[expose] def R16_33_close (D : Data G) : Prop :=
  ∀ (V₀ V L : Subgroup G) (hV : IsElemAbelian 2 V), Sect16 D V₀ V L hV → ∀ m : ℕ,
    Case1633 D V₀ V hV L m →
      m = 2 → V₀ = ⊥ → ¬ centralizer (E3.cClos V 2 D.T : Set G) ≤ D.M →
        (calOStar 2 D.M V₀ V).Nonempty

@[expose] def R16_40 (D : Data G) : Prop :=
  ∀ (V₀ V L : Subgroup G) (hV : IsElemAbelian 2 V), Sect16 D V₀ V L hV →
    ¬ Case167_1 D V₀ V hV L

@[expose] def R16_41 (D : Data G) : Prop :=
  ∀ (V₀ V L : Subgroup G) (hV : IsElemAbelian 2 V), Sect16 D V₀ V L hV →
    Case167_1 D V₀ V hV L →
      (∃ Q : Vtil V₀ V hV → ZMod 2, IsMinusQuadF2 Q ∧ QuadInvariant Q (lBar V₀ V hV L)) ∧
      ∀ Q : Vtil V₀ V hV → ZMod 2, IsMinusQuadF2 Q → QuadInvariant Q (lBar V₀ V hV L) →
        (∀ w : Vtil V₀ V hV, w ≠ 1 → Q w = 0 → IsE16A5 ↥(ptCent (lBar V₀ V hV L) w)) ∧
        ∀ w : Vtil V₀ V hV, Q w ≠ 0 →
          IsSym ↥(ptCent (lBar V₀ V hV L) w) 6 ∧
            ∀ x : IntMod V hV, mkTil V₀ V hV x = w → centralizer ({x.val} : Set G) ≤ D.M

@[expose] def R16_42 (D : Data G) : Prop :=
  ∀ (V₀ V L : Subgroup G) (hV : IsElemAbelian 2 V), Sect16 D V₀ V L hV →
    Case167_1 D V₀ V hV L →
      ((mSub V₀ + 4 : ℕ) : ℕ∞) ≤ rMV D.M V ∧ (2 : ℕ∞) ≤ deltaInf D.M V ∧
        (V₀ = ⊥ → (4 : ℕ∞) < rMV D.M V)

@[expose] def R16_43_1 (D : Data G) : Prop :=
  ∀ (V₀ V L : Subgroup G) (hV : IsElemAbelian 2 V), Sect16 D V₀ V L hV →
    Case167_1 D V₀ V hV L →
      ∀ (i : ℕ) (A : Subgroup G) (g : G), Hyp1643 D V₀ V i A g →
        barSub V₀ V hV A ≤ lBar V₀ V hV L

@[expose] def R16_43_2 (D : Data G) : Prop :=
  ∀ (V₀ V L : Subgroup G) (hV : IsElemAbelian 2 V), Sect16 D V₀ V L hV →
    Case167_1 D V₀ V hV L →
      ∀ (i : ℕ) (A : Subgroup G) (g : G), Hyp1643 D V₀ V i A g →
        i = 0 → barSub V₀ V hV A ≠ ⊥ → barSub V₀ V hV A ∈ calABar 2 D.M V₀ V hV

@[expose] def R16_43_3 (D : Data G) : Prop :=
  ∀ (V₀ V L : Subgroup G) (hV : IsElemAbelian 2 V), Sect16 D V₀ V L hV →
    Case167_1 D V₀ V hV L → normalizer (E3.wClos V 0 D.T : Set G) ≤ D.M

@[expose] def R16_43_4 (D : Data G) : Prop :=
  ∀ (V₀ V L : Subgroup G) (hV : IsElemAbelian 2 V), Sect16 D V₀ V L hV →
    Case167_1 D V₀ V hV L →
      ∀ (i : ℕ) (A : Subgroup G) (g : G), Hyp1643 D V₀ V i A g →
        V₀ = ⊥ → V ≤ conjSubgroup D.M g ∨
          (conjSubgroup V g ∈ calOStar 1 D.M V₀ V ∧ IsQ8FourDih ↥(V ⊔ conjSubgroup V g))

@[expose] def R16_44 (D : Data G) : Prop :=
  ∀ (V₀ V L : Subgroup G) (hV : IsElemAbelian 2 V), Sect16 D V₀ V L hV →
    Case167_1 D V₀ V hV L → calO 1 D.M V₀ V = calO1 1 D.M V₀ V

@[expose] def R16_45 (D : Data G) : Prop :=
  ∀ (V₀ V L : Subgroup G) (hV : IsElemAbelian 2 V), Sect16 D V₀ V L hV →
    Case167_1 D V₀ V hV L → calO 1 D.M V₀ V = calOStar 1 D.M V₀ V

@[expose] def R16_46 (D : Data G) : Prop :=
  ∀ (V₀ V L : Subgroup G) (hV : IsElemAbelian 2 V), Sect16 D V₀ V L hV →
    Case167_1 D V₀ V hV L → L ∈ calC D.M → IsU4 (Bar2 L) 1 →
      ∀ x : IntMod V hV, Setup1645 D V hV x → Concl1646 L x.val

@[expose] def R16_47_close (D : Data G) : Prop :=
  ∀ (V₀ V L : Subgroup G) (hV : IsElemAbelian 2 V), Sect16 D V₀ V L hV →
    Case167_1 D V₀ V hV L → L ∈ calC D.M → IsU4 (Bar2 L) 1 →
      ∀ x : IntMod V hV, Setup1645 D V hV x → Concl1647 V x.val → Concl1647a D V₀ V x.val →
        Concl1647c L x.val

@[expose] def R16_48 (D : Data G) : Prop :=
  ∀ (V₀ V L : Subgroup G) (hV : IsElemAbelian 2 V), Sect16 D V₀ V L hV →
    ¬ Case167_4 D V₀ V hV L

@[expose] def R16_50 (D : Data G) : Prop :=
  ∀ (V₀ V L : Subgroup G) (hV : IsElemAbelian 2 V), Sect16 D V₀ V L hV →
    Case167_4 D V₀ V hV L →
      ((mSub V₀ + 4 : ℕ) : ℕ∞) ≤ rMV D.M V ∧ (2 : ℕ∞) ≤ deltaInf D.M V ∧
        (V₀ = ⊥ → (4 : ℕ∞) < rMV D.M V)

@[expose] def R16_53 (D : Data G) : Prop :=
  ∀ (V₀ V L : Subgroup G) (hV : IsElemAbelian 2 V), Sect16 D V₀ V L hV →
    Case167_4 D V₀ V hV L → ⁅E3.wClos V 0 D.T, V⁆ = ⊥

@[expose] def R16_54 (D : Data G) : Prop :=
  ∀ (V₀ V L : Subgroup G) (hV : IsElemAbelian 2 V), Sect16 D V₀ V L hV →
    Case167_4 D V₀ V hV L → calO2 1 D.M V₀ V = ∅

@[expose] def R16_55 (D : Data G) : Prop :=
  ∀ (V₀ V L : Subgroup G) (hV : IsElemAbelian 2 V), Sect16 D V₀ V L hV →
    Case167_4 D V₀ V hV L →
      V₀ = ⊥ ∧ ¬ centralizer (E3.cClos V 1 D.T : Set G) ≤ D.M

@[expose] def R16_56 (D : Data G) : Prop :=
  ∀ (V₀ V L : Subgroup G) (hV : IsElemAbelian 2 V), Sect16 D V₀ V L hV →
    Case167_4 D V₀ V hV L → V₀ = ⊥ → ⁅E3.wClos V 1 D.T, V⁆ = ⊥

@[expose] def R16_57 (D : Data G) : Prop :=
  ∀ (V₀ V L : Subgroup G) (hV : IsElemAbelian 2 V), Sect16 D V₀ V L hV →
    ¬ Case167_7 D V₀ V hV L

@[expose] def R16_63a (D : Data G) : Prop :=
  ∀ (V₀ V L : Subgroup G) (hV : IsElemAbelian 2 V), Sect16 D V₀ V L hV →
    (Case167_2 D V₀ V hV L ∨ Case167_3 D V₀ V hV L) → Hyp154 D V₀ V L

@[expose] def R16_63 (D : Data G) : Prop :=
  ∀ (V₀ V L : Subgroup G) (hV : IsElemAbelian 2 V), Sect16 D V₀ V L hV →
    Sit1663 D V₀ V hV L →
      ⁅E3.wClos V 0 D.T, V⁆ = ⊥ ∧ normalizer (E3.wClos V 0 D.T : Set G) ≤ D.M

@[expose] def R16_64 (D : Data G) : Prop :=
  ∀ (V₀ V L : Subgroup G) (hV : IsElemAbelian 2 V), Sect16 D V₀ V L hV →
    Sit1663 D V₀ V hV L → ¬ Case167_2 D V₀ V hV L

@[expose] def R16_67 (D : Data G) : Prop :=
  ∀ (V₀ V L : Subgroup G) (hV : IsElemAbelian 2 V), Sect16 D V₀ V L hV →
    Sit1665 D V₀ V hV L → calO 1 D.M V₀ V = ∅

@[expose] def R16_67_pre (D : Data G) : Prop :=
  ∀ (V₀ V L : Subgroup G) (hV : IsElemAbelian 2 V), Sect16 D V₀ V L hV →
    Sit1665 D V₀ V hV L → ∀ g : G, conjSubgroup V g ∈ calO 1 D.M V₀ V →
      Concl1667pre D V₀ V L hV g

@[expose] def R16_67a (D : Data G) : Prop :=
  ∀ (V₀ V L : Subgroup G) (hV : IsElemAbelian 2 V), Sect16 D V₀ V L hV →
    Sit1665 D V₀ V hV L → ∀ g : G, conjSubgroup V g ∈ calO 1 D.M V₀ V →
      Concl1667pre D V₀ V L hV g → False

@[expose] def R16_68 (D : Data G) : Prop :=
  ∀ (V₀ V L : Subgroup G) (hV : IsElemAbelian 2 V), Sect16 D V₀ V L hV →
    Sit1665 D V₀ V hV L →
      V₀ = ⊥ ∧ ¬ centralizer (E3.cClos V 1 D.T : Set G) ≤ D.M

@[expose] def R16_68_k (D : Data G) : Prop :=
  ∀ (V₀ V L : Subgroup G) (hV : IsElemAbelian 2 V), Sect16 D V₀ V L hV →
    Sit1665 D V₀ V hV L → CFSG.RankThree.PartOne.IsStronglyPEmbedded 3 D.M

@[expose] def R16_68_close (D : Data G) : Prop :=
  ∀ (V₀ V L : Subgroup G) (hV : IsElemAbelian 2 V), Sect16 D V₀ V L hV →
    Sit1665 D V₀ V hV L → V₀ = ⊥ →
      ∀ (A : Subgroup G) (g : G), A ∈ E3.gammaSet V 1 D.T → barSub V₀ V hV A ≠ ⊥ →
        A ≤ conjSubgroup V g →
          rk ↥(barSub V₀ V hV A) = 2 ∧ gammaOneBar V A ≤ conjSubgroup D.M g ∧
            (gammaOneBar V A).relIndex V ≤ 2

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
