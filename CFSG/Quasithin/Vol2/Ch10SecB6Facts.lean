module

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Vol2NativeBasicBase
public import CFSG.Quasithin.Background.B2FactorizationResidual
public import CFSG.Quasithin.Vol2.Ch10StatementsA

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecB

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.H13 CFSG.Assembly.LowTwoRank

@[expose] def Fact10_2_6Pair : Prop :=
  ∀ (Q : Type) [Group Q], Vol2Native.SQTKHypCat Q → ∀ S K B₁ B₂ : Subgroup Q,
    IsSylowTwoOf S ⊤ → K ∈ cComp (⊤ : Subgroup Q) → B₁ ∈ lFamily S → B₂ ∈ lFamily S →
    S ≤ Subgroup.normalizer (B₁ : Set Q) → S ≤ Subgroup.normalizer (B₂ : Set Q) →
    B₁ ≤ K → B₂ ≤ K → ⁅B₁, B₂⁆ ≤ pCoreOf 2 B₁ ⊓ pCoreOf 2 B₂ →
    Nonempty (ModO2 B₁ ≃* ModO2 B₂) → False

@[expose] def Fact10_2_6Rank : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (B L : Subgroup X), A312Case B L →
    (((∃ n : ℕ, CFSG.Blueprint.SuzukiModel (ModO2 B) 2 n) ∨
        Nonempty (ModO2 B ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2))) →
      ∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ p ∣ Nat.card (ModO2 B) ∧ 2 ≤ CFSG.Open.pRank p L) ∧
    ((Nonempty (ModO2 B ≃* alternatingGroup (Fin 5)) ∨
        ∃ n : ℕ, 2 ≤ n ∧ ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = 2 ^ n ∧
          Nonempty (ModO2 B ≃* Matrix.SpecialLinearGroup (Fin 2) F)) →
      (∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ p ∣ Nat.card (ModO2 B) ∧ 2 ≤ CFSG.Open.pRank p L) ∨
        (CFSG.pCore 2 ↥B = ⊥ ∧ (A312C8 B L ∨ A312C15 B L)))

@[expose] def Gap10_2_6Nonquasi : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L I : Subgroup G), Hyp10 G T L I →
    ∀ H : Subgroup G, InM (fsuL0 T L ⊔ T1 T L) H → H ≠ fsuM T L →
    ∀ X K : Subgroup G, IsLi T L X → K ∈ cComp H → X < K → CharTwo K →
      A312Nonquasi (modO2Image H X) (modO2Image H K) →
      modO2Image H K ≠ modO2Image H X ⊔
        (CFSG.oddCore ↥(modO2Image H K)).map (modO2Image H K).subtype →
      False

end CFSG.Quasithin.Vol2.Ch10.SecB
