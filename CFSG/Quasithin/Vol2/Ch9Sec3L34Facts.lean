module

public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Quasithin.Background.A3Structure312Defs
public import CFSG.Quasithin.Vol2.Ch5Statements

public section

namespace CFSG.Quasithin.H13.Ch9

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique

@[expose] def FactM23L34Inner : Prop :=
  ∀ (Γ : Type) [Group Γ] [Finite Γ] (L A R : Subgroup Γ), IsSporadic .M23 ↥L → A ≤ L →
    IsSL3Ch5 2 (ModO2 A) → R ≤ Subgroup.normalizer (L : Set Γ) →
    R ≤ Subgroup.normalizer (A : Set Γ) → Odd (Nat.card R) →
    ∀ r ∈ R, ∃ a ∈ A, ∀ x ∈ A, r * x * r⁻¹ = a * x * a⁻¹

end CFSG.Quasithin.H13.Ch9
