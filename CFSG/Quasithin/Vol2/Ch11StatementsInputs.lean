module

public import CFSG.Quasithin.Vol2.Ch10StatementsInputs
public import CFSG.Quasithin.Vol2.Ch4Sec2W4213
public import CFSG.Quasithin.Background.C2Blocks

public section

namespace CFSG.Quasithin.Vol2.Ch11

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13
open CFSG.Assembly.LowTwoRank (StatedSL)
open scoped IsMulCommutative Pointwise

section Defs

variable {G : Type} [Group G]

@[expose] def IsIrrSection (X J C : Subgroup G) : Prop :=
  C < J ∧ X ≤ Subgroup.normalizer (J : Set G) ∧ X ≤ Subgroup.normalizer (C : Set G) ∧
    ∀ W : Subgroup G, C ≤ W → W ≤ J → X ≤ Subgroup.normalizer (W : Set G) → W = C ∨ W = J

@[expose] def IsSemisimpleSection (X U C : Subgroup G) : Prop :=
  ∀ W : Subgroup G, C ≤ W → W ≤ U → X ≤ Subgroup.normalizer (W : Set G) →
    ∃ W' : Subgroup G, C ≤ W' ∧ W' ≤ U ∧ X ≤ Subgroup.normalizer (W' : Set G) ∧
      W ⊓ W' = C ∧ W ⊔ W' = U

@[expose] def IsNotation4211 (T M L I : Subgroup G) : Prop :=
  I ≤ M ∧ (L : Set G) ⊆ (I : Set G) * (pCoreOf 2 (L ⊔ T) : Set G) ∧
    conjSubgroupsBy T L = conjSubgroupsBy I L ∧ pCoreOf 2 I ≠ ⊥

@[expose] def xiP (L : Subgroup G) (p : ℕ) : Subgroup G :=
  oTwoUpper (preimageModTwoCore L
    (Subgroup.closure {x | x ∈ CFSG.pCore p (↥L ⧸ CFSG.pCore 2 ↥L) ∧ x ^ p = 1}))

abbrev v4213 (T L : Subgroup G) : Subgroup G := ⁅reducedAggregate (L ⊔ T), L⁆

@[expose] def Cases4_2_13 (T M L I : Subgroup G) : Prop :=
  (∃ (n : ℕ) (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = 2 ^ n ∧
      Nonempty (↥L ⧸ CFSG.pCore 2 ↥L ≃* Matrix.SpecialLinearGroup (Fin 2) F)) ∨
    (∃ d : ℕ, (d = 3 ∨ d = 4) ∧
      Nonempty (↥L ⧸ CFSG.pCore 2 ↥L ≃* Matrix.SpecialLinearGroup (Fin d) (ZMod 2)) ∧
      ∃ _ : IsMulCommutative ↥(v4213 T L),
        (∃ k : ℕ, 0 < k ∧ DirectSumOfCopies (V := ↥(v4213 T L)) (autOn L (v4213 T L)) ⊤
            ((Subgroup.centralizer (L : Set G)).subgroupOf (v4213 T L))
            (FFModel.nat (StatedSL d (ZMod 2))) k) ∨
          (d = 4 ∧ SLExteriorTwo (V := ↥(v4213 T L)) (autOn L (v4213 T L)) ⊤
            ((Subgroup.centralizer (L : Set G)).subgroupOf (v4213 T L)) 4)) ∨
    (IsAltBlockType (oTwoUpper (I ⊓ L)) 6 ∨ IsExcA7Block (oTwoUpper (I ⊓ L))) ∨
    (IsHatA6Block (oTwoUpper (I ⊓ L)) ∧
      ∀ z ∈ v4213 T L ⊓ Subgroup.centralizer (T : Set G), z ≠ 1 →
        ¬ v4213 T L ≤ pCoreOf 2 (Subgroup.centralizer ({z} : Set G))) ∨
    (IsG2Block (oTwoUpper (I ⊓ L)) ∧
      (Nat.card (v4213 T L) = 2 ^ 6 →
        ∃ V₃ : Subgroup G, V₃ ≤ v4213 T L ∧ Nat.card V₃ = 2 ^ 3 ∧
          T ⊓ I ≤ Subgroup.normalizer (V₃ : Set G) ∧ ¬ Subgroup.centralizer (V₃ : Set G) ≤ M))

end Defs

@[expose] def TmpL6_3_2_2_four : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L I : Subgroup G), FSU G T L I →
    fsuCVM T L I = conjClosure (I ⊓ Subgroup.centralizer (fsuL0 T L : Set G)) (fsuM T L) ∧
    fsuCVM T L I =
      conjClosure (fsuV T I ⊓ Subgroup.centralizer (fsuL0 T L : Set G)) (fsuM T L)

@[expose] def TmpL6_3_2_2_six : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L I : Subgroup G), FSU G T L I →
    fsuCVM T L I ≠ ⊥ → IsUniqueM (fsuL0 T L ⊔ T) (fsuM T L) →
      fsuL0 T L = ⁅fsuL0 T L, thompsonJ T⁆ ∧
        ∃ _ : IsMulCommutative ↥(fsuV T I),
          IsFFModule (V := ↥(fsuV T I)) (autOn (fsuL0 T L ⊔ T) (fsuV T I))

@[expose] def TmpL6_3_2_14 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L : Subgroup G), IsSimpleGroup G →
    (∃ a b : G, a * b ≠ b * a) → QuasithinUnique.quasithinIsQTKECat G →
    quasithinIsSylowTwo T → quasithinIsLocal T L → ¬ CFSG.IsQuasisimple (↥L ⧸ CFSG.pCore 2 ↥L) →
      solvRad L ≤ Subgroup.centralizer (reducedAggregate (L ⊔ T) : Set G)

@[expose] def TmpL6_4_2_13 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M L I : Subgroup G), Ch10.TmpL6_Hyp4_2_1 G T M L →
    IsNotation4211 T M L I →
      IsUniqueM I M ∨ ((Concl443TwoI G T M L (v4213 T L) ∧ IrrCase4213 G L (v4213 T L)) ∨
        Orth4213 G M L (v4213 T L))

@[expose] def Tmp1_3_3 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L : Subgroup G) (p : ℕ), IsSimpleGroup G →
    (∃ a b : G, a * b ≠ b * a) → QuasithinUnique.quasithinIsQTKECat G →
    quasithinIsSylowTwo T → quasithinIsLocal T L → ¬ CFSG.IsQuasisimple (↥L ⧸ CFSG.pCore 2 ↥L) →
    p.Prime → p ≠ 2 → p ∣ Nat.card (CFSG.fittingSubgroup (↥L ⧸ CFSG.pCore 2 ↥L)) →
      IsXi T (xiP L p)

end CFSG.Quasithin.Vol2.Ch11
