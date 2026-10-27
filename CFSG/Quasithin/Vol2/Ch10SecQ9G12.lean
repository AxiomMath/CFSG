module

public import CFSG.Quasithin.Background.F1Models
public import CFSG.Quasithin.Vol2.Ch10SecKGA318
public import Certificates.Data.CFSGNative.H13.J4Chain

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecC.C10P4F

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.H13 CFSG.QuasithinUnique

@[expose] def FactK7L4 : Prop :=
  ∀ (X : Type) [Group X] (s : Bool) (r e : ℕ), IsPSLEps3 s r e X →
    ∀ f : X →* Matrix.SpecialLinearGroup (Fin 4) (ZMod 2), ¬ Function.Surjective f

@[expose] def FactK7L5 : Prop :=
  ∀ (X : Type) [Group X] (s : Bool) (r e : ℕ), IsPSLEps3 s r e X →
    ∀ f : X →* Matrix.SpecialLinearGroup (Fin 5) (ZMod 2), ¬ Function.Surjective f

@[expose] def FactL4Aut : Prop :=
  ∀ (X S : Subgroup (Matrix.SpecialLinearGroup (Fin 4) (ZMod 2))), IsSylowTwoOf S ⊤ →
    S ≤ Subgroup.normalizer (X : Set (Matrix.SpecialLinearGroup (Fin 4) (ZMod 2))) →
    ⁅X, X⁆ = X → Nonempty (↥X ⧸ CFSG.pCore 2 ↥X ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) →
    ∀ α : MulAut (Matrix.SpecialLinearGroup (Fin 4) (ZMod 2)), (∀ x ∈ X, α x ∈ X) →
      ∃ g ∈ X, ∀ x ∈ X, α x = g * x * g⁻¹

@[expose] def FactL5Inv : Prop :=
  ∀ (X S : Subgroup (Matrix.SpecialLinearGroup (Fin 5) (ZMod 2))), IsSylowTwoOf S ⊤ →
    S ≤ Subgroup.normalizer (X : Set (Matrix.SpecialLinearGroup (Fin 5) (ZMod 2))) →
    ⁅X, X⁆ = X → Nonempty (↥X ⧸ CFSG.pCore 2 ↥X ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) →
    ∀ y ∈ Subgroup.normalizer (X : Set (Matrix.SpecialLinearGroup (Fin 5) (ZMod 2))),
      orderOf y = 3 → (∀ x ∈ X, y * x * y⁻¹ * x⁻¹ ∈ pCoreOf 2 X) →
      ∃ r ∈ S, ∃ k : ℕ, (r * y * r⁻¹ * y) ^ 2 ^ k = 1

end CFSG.Quasithin.Vol2.Ch10.SecC.C10P4F
