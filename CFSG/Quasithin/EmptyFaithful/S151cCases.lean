module

public import CFSG.Quasithin.EmptyFaithful.S151Statements

public section

namespace CFSG.Quasithin

open CFSG.Open

section Cases151c

variable {V : Type} [CommGroup V]

@[expose] def AElementaryNine (X A₀ : Subgroup (MulAut V)) : Prop :=
  IsElemAbelian 3 (oTwoUpper X) ∧ Nat.card (oTwoUpper X) = 9 ∧
    ∃ t : MulAut V, orderOf t = 2 ∧ (∀ x ∈ oTwoUpper X, t * x * t⁻¹ = x⁻¹) ∧
      A₀ = oTwoUpper X ⊔ Subgroup.zpowers t

@[expose] def AExtraspecialThree (X Tb A₀ : Subgroup (MulAut V)) : Prop :=
  IsPOnePlusTwo 3 ↥(oTwoUpper X) ∧
    (∃ t : MulAut V, orderOf t = 2 ∧
      (∀ x ∈ oTwoUpper X, t * x * t⁻¹ * x ∈ frattiniIn (oTwoUpper X)) ∧
      A₀ = oTwoUpper X ⊔ Subgroup.zpowers t) ∧
    IsIrredOnSection Tb (oTwoUpper X) (frattiniIn (oTwoUpper X))

@[expose] def ACase1 (X A₀ : Subgroup (MulAut V)) : Prop :=
  Nat.card V = 16 ∧ X = A₀ ∧ Nonempty (↥A₀ ≃* DihedralGroup 3)

@[expose] def ACase2 (X A₀ : Subgroup (MulAut V)) : Prop :=
  Nat.card V = 16 ∧ Nonempty (↥A₀ ≃* DihedralGroup 3) ∧
    Nonempty (↥X ≃* DihedralGroup 3 × Multiplicative (ZMod 3))

@[expose] def ACase3 (X A₀ : Subgroup (MulAut V)) : Prop :=
  Nat.card V = 16 ∧ X = A₀ ∧ IsOmegaFourPlus X

@[expose] def ACase4 (X Tb A₀ : Subgroup (MulAut V)) : Prop :=
  Nat.card V = 16 ∧ AElementaryNine X A₀ ∧ Nonempty (↥Tb ≃* Multiplicative (ZMod 4))

@[expose] def ACase5 (X Tb A₀ : Subgroup (MulAut V)) : Prop :=
  Nat.card V = 16 ∧ Nonempty (↥A₀ ≃* DihedralGroup 5) ∧
    (Nonempty (↥Tb ≃* Multiplicative (ZMod 2)) ∨ Nonempty (↥Tb ≃* Multiplicative (ZMod 4))) ∧
    (fittingOf X = fittingOf A₀ ∨ Nonempty (↥(fittingOf X) ≃* Multiplicative (ZMod 15)))

@[expose] def ACase6 (Tb A₀ : Subgroup (MulAut V)) (p : ℕ) : Prop :=
  Nat.card V = 256 ∧ ∃ A₁ A₂ : Subgroup (MulAut V), IsInternalDirect A₀ A₁ A₂ ∧
    Nonempty (↥A₁ ≃* DihedralGroup p) ∧ Nonempty (↥A₂ ≃* DihedralGroup p) ∧
    (∃ t ∈ Tb, conjBy t A₁ = A₂) ∧ commV A₁ ⊓ commV A₂ = ⊥ ∧ commV A₁ ⊔ commV A₂ = ⊤

@[expose] def ACase7 (X Tb A₀ : Subgroup (MulAut V)) : Prop :=
  Nat.card V = 64 ∧ AExtraspecialThree X Tb A₀

@[expose] def IsOFourPlusAct (X : Subgroup (MulAut V)) : Prop :=
  Nat.card V = 16 ∧ ∃ q : V → ZMod 2, IsQuadraticFormOn q ∧ IsNondegQuadratic q ∧
    IsPlusType q ∧ X = orthogonalGroupOf q

@[expose] def TwoNilpAut (X : Subgroup (MulAut V)) : Prop :=
  ∃ N : Subgroup (MulAut V), N ≤ X ∧ (∀ g ∈ X, ∀ y ∈ N, g * y * g⁻¹ ∈ N) ∧
    Odd (Nat.card N) ∧ ∀ x ∈ X, ∃ k : ℕ, x ^ 2 ^ k ∈ N

theorem twoNilp_of_oTwoUpper_odd [Finite V] {X : Subgroup (MulAut V)}
    (hodd : Odd (Nat.card (oTwoUpper X))) : TwoNilpAut X :=
  ⟨oTwoUpper X, oTwoUpper_le X, fun _ hg y hy =>
    (Subgroup.mem_normalizer_iff.mp (le_normalizer_oTwoUpper X hg) y).mp hy, hodd,
    fun _ hx => exists_pow_mem_oTwoUpper X hx⟩

@[expose] def Cases7Aut (X Tb A₀ : Subgroup (MulAut V)) : Prop :=
  ACase1 X A₀ ∨ ACase2 X A₀ ∨ ACase3 X A₀ ∨ ACase4 X Tb A₀ ∨ ACase5 X Tb A₀ ∨
    (∃ p : ℕ, (p = 3 ∨ p = 5) ∧ ACase6 Tb A₀ p) ∨ ACase7 X Tb A₀

end Cases151c

end CFSG.Quasithin
