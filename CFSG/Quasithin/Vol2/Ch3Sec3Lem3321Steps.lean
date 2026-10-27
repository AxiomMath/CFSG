module

public import CFSG.Quasithin.Background.B5Statement
public import CFSG.Quasithin.Vol2.Ch3Sec3Setup

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank
open scoped IsMulCommutative

variable {G : Type} [Group G]

@[expose] def Mod3321Ext (T L : Subgroup G) [IsMulCommutative ↥(vPlus L T)] : Prop :=
  ∃ Z₀ : Subgroup ↥(vPlus L T),
    Z₀ ≤ fixV (autOn L (vPlus L T)) ⊓ commV (autOn L (vPlus L T)) ∧ Nat.card ↥Z₀ ≤ 2 ∧
      SLExteriorTwo (autOn L (vPlus L T)) (commV (autOn L (vPlus L T))) Z₀ 4

@[expose] def Mod3321Sum (T L : Subgroup G) [IsMulCommutative ↥(vPlus L T)] : Prop :=
  SumNatDual (autOn L (vPlus L T)) (commV (autOn L (vPlus L T))) 4

@[expose] def Mod3321 (T L : Subgroup G) : Prop :=
  ∃ _ : IsMulCommutative ↥(vPlus L T), Mod3321Ext T L ∨ Mod3321Sum T L

@[expose] def Step3_3_21d : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M L D : Subgroup G), Hyp331 G T M L D →
    Nonempty (↥(autOn L (vPlus L T)) ≃* Matrix.SpecialLinearGroup (Fin 4) (ZMod 2)) →
    Mod3321 T L →
      Subgroup.normalizer ((pCoreOf 2
        (L ⊓ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) ⊔ T)) : Set G) ≤ M

@[expose] def Step3_3_21e : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M L D : Subgroup G), Hyp331 G T M L D →
    Nonempty (↥(autOn L (vPlus L T)) ≃* Matrix.SpecialLinearGroup (Fin 4) (ZMod 2)) →
    Mod3321 T L → quasithinOmegaOneCenter T ⊓ Subgroup.centralizer (L : Set G) = ⊥

@[expose] def Step3_3_21f : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M L D : Subgroup G), Hyp331 G T M L D →
    Nonempty (↥(autOn L (vPlus L T)) ≃* Matrix.SpecialLinearGroup (Fin 4) (ZMod 2)) →
    Mod3321 T L → ¬ InducesInnerOn T L

@[expose] def Step3_3_21gExt : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M L D : Subgroup G), Hyp331 G T M L D →
    Nonempty (↥(autOn L (vPlus L T)) ≃* Matrix.SpecialLinearGroup (Fin 4) (ZMod 2)) →
    ∀ _ : IsMulCommutative ↥(vPlus L T), Mod3321Ext T L → InducesInnerOn T L

@[expose] def Step3_3_21gSum : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M L D : Subgroup G), Hyp331 G T M L D →
    Nonempty (↥(autOn L (vPlus L T)) ≃* Matrix.SpecialLinearGroup (Fin 4) (ZMod 2)) →
    ∀ _ : IsMulCommutative ↥(vPlus L T), Mod3321Sum T L → InducesInnerOn T L

end CFSG.Quasithin.H13
