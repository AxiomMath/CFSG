module

public import CFSG.Quasithin.Vol2.Ch3Sec1L319Form
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Quasithin.EmptyFaithful.S1422Basic
public import CFSG.Quasithin.Vol2.Ch10StatementsInputsAS
public import CFSG.Quasithin.Vol2.Ch1Xi
public import CFSG.Quasithin.Vol2.Ch8Sec2Statements

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Quasithin.E3 CFSG.Quasithin.H CFSG.Quasithin.ASInputs CFSG.Quasithin
  CFSG.Quasithin.H13.L319
open scoped IsMulCommutative

@[expose] def M22Facts822 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L I : Subgroup G), Hyp7_0_2 G T L I → Hyp7_3_1 T L I →
    Hyp8_2_1 T L I → ∀ _ : IsMulCommutative ↥(fsuV T I), Case8_2 T L I →
      Row711M22Code T L I → ¬ autOn T (fsuV T I) ≤ autOn (fsuL0 T L) (fsuV T I) →
      ∀ hV : IsElemAbelian 2 (fsuV T I),
        qInt (fsuL0 T L ⊔ T) (fsuV T I) hV = 2 ∧ ¬ IsDualFFInt (fsuL0 T L ⊔ T) (fsuV T I) hV ∧
        Six6i T (fsuM T L) (fsuV T I) ∧ 2 ≤ qMin (fsuM T L) (fsuV T I) hV ∧
        Six6iiiImg T (fsuM T L) (fsuV T I)

@[expose] def CoverM22 {G : Type} [Group G] [Finite G] (T L : Subgroup G) : Prop :=
  ∃ _ : ((pCoreOf 2 (fsuL0 T L)).subgroupOf (fsuL0 T L)).Normal,
    IsHat (↥(fsuL0 T L) ⧸ (pCoreOf 2 (fsuL0 T L)).subgroupOf (fsuL0 T L))
      (CFSG.Blueprint.NativeSporadic.Carrier .M22)

@[expose] def Res822ThreeCover : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L I : Subgroup G), Hyp7_0_2 G T L I → Hyp7_3_1 T L I →
    Hyp8_2_1 T L I → ∀ _ : IsMulCommutative ↥(fsuV T I), Case8_2 T L I →
      Row711M22Code T L I → ¬ autOn T (fsuV T I) ≤ autOn (fsuL0 T L) (fsuV T I) →
      ¬ NoThreeInCV (fsuM T L) (fsuV T I) → CoverM22 T L

@[expose] def Res822CoverJ3 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L I : Subgroup G), Hyp7_0_2 G T L I → Hyp7_3_1 T L I →
    Hyp8_2_1 T L I → ∀ _ : IsMulCommutative ↥(fsuV T I), Case8_2 T L I →
      Row711M22Code T L I → ¬ autOn T (fsuV T I) ≤ autOn (fsuL0 T L) (fsuV T I) →
      CoverM22 T L → ∀ H : Subgroup G, IsHStar T (fsuM T L) H → fsuV T I ≤ pCoreOf 2 H →
        KerNoThree (fsuM T L) H

@[expose] def Res822Kz : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L I : Subgroup G), Hyp7_0_2 G T L I → Hyp7_3_1 T L I →
    Hyp8_2_1 T L I → ∀ _ : IsMulCommutative ↥(fsuV T I), Case8_2 T L I →
      Row711M22Code T L I → ¬ autOn T (fsuV T I) ≤ autOn (fsuL0 T L) (fsuV T I) →
      ∀ H : Subgroup G, IsHStar T (fsuM T L) H → fsuV T I ≤ pCoreOf 2 H →
        IsXi T (twoResidual H) →
        (∃ φ : ↥H →* (Equiv.Perm (Fin 3) ≀ᵣ Multiplicative (ZMod 2)),
          Function.Surjective φ ∧ φ.ker = (pCoreOf 2 H).subgroupOf H) → False

end CFSG.Quasithin.H13
