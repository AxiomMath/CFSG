module

public import CFSG.Quasithin.Vol2.Ch5Statements
public import CFSG.Quasithin.Recognition.F112WChief

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin

@[expose] def L34IrredParabolicFact : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (K U A B : Subgroup G), LieModel (O2Q K) .PSL 3 2 2 →
    pCoreOf 2 K ≤ U → U ≤ K →
    (∀ x ∈ U, ∀ y ∈ U, x * y * x⁻¹ * y⁻¹ ∈ pCoreOf 2 K) → (∀ x ∈ U, x ^ 2 ∈ pCoreOf 2 K) →
    Nat.card U = 16 * Nat.card (pCoreOf 2 K) →
    IsChiefStep K (pCoreOf 2 K) B A → ¬ IsCentralStep K B A →
      ∀ m : ℕ, F112W.IsChiefSeriesBetween (oTwoUpper (K ⊓ Subgroup.normalizer (U : Set G)))
        (pCoreOf 2 (oTwoUpper (K ⊓ Subgroup.normalizer (U : Set G))))
        (⁅A, oTwoUpper (K ⊓ Subgroup.normalizer (U : Set G))⁆ ⊓ B)
        ⁅A, oTwoUpper (K ⊓ Subgroup.normalizer (U : Set G))⁆ m → 2 ≤ m

end CFSG.Quasithin.H13
