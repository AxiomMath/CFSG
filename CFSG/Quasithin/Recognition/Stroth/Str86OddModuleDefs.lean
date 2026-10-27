module

public import CFSG.Quasithin.Recognition.Stroth.Str86ZTwoOrth
public import CFSG.Quasithin.Recognition.Stroth.L2ChiefNatural

public section

namespace CFSG.Quasithin.Stroth

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.F112R
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

@[expose] def Str86OddModule (L1 L2 S : Subgroup G) (m : ℕ) : Prop :=
  (∃ (hstep : IsChiefStep (u3H L1 L2 S) (Q2 L1 L2 S) ⊥ ⁅Z2 L1 L2 S, u3H L1 L2 S⁆)
      (hE : IsElemAbelian 2 (Ch3z.chiefMod ⊥ ⁅Z2 L1 L2 S, u3H L1 L2 S⁆)),
      IsNaturalChiefStep (u3H L1 L2 S) (Q2 L1 L2 S) ⊥ ⁅Z2 L1 L2 S, u3H L1 L2 S⁆ hstep
        (q2_le_u3H L1 L2 S) hE m) ∧
    Z1 L1 L2 S ≤ ⁅Z2 L1 L2 S, u3H L1 L2 S⁆ ∧
    Nat.card (Z1 L1 L2 S) = 2 ^ m ∧
    (∀ x ∈ S, x ∉ Q2 L1 L2 S → ⁅Z2 L1 L2 S, Subgroup.zpowers x⁆ = Z1 L1 L2 S) ∧
    ∀ g ∈ P1 L1 L2 S, g ∉ bigB L1 L2 S →
      ⁅Z2 L1 L2 S, u3H L1 L2 S⁆ ⊓ (MulAut.conj g • ⁅Z2 L1 L2 S, u3H L1 L2 S⁆) = Z1 L1 L2 S

@[expose] def Str86OddModuleOf : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L1 L2 S : Subgroup G) (k m : ℕ) (F : Type) [Field F]
    [Finite F],
    F112Hyp L1 L2 S → bigB L1 L2 S ≤ Subgroup.normalizer (S : Set G) →
    2 ≤ k → Nat.card F = (2 ^ k) ^ 2 →
    (Nonempty (oTwoQuot ↥L1 ≃* StatedSU 3 (2 ^ k) F) ∨
      Nonempty (oTwoQuot ↥L1 ≃* StatedProj (StatedSU 3 (2 ^ k) F))) →
    VBig L2 → IsL2Quot m (oTwoQuot ↥L2) → 2 * k ≤ m →
    L1 ⊔ Q1 L1 L2 S ≤ Subgroup.centralizer (Z1 L1 L2 S : Set G) →
    Z2 L1 L2 S ≤ Q1 L1 L2 S →
    (∀ x ∈ conjClosure (Z2 L1 L2 S) L1, ∀ y ∈ conjClosure (Z2 L1 L2 S) L1, x * y = y * x) →
      Str86OddModule L1 L2 S m

end CFSG.Quasithin.Stroth
