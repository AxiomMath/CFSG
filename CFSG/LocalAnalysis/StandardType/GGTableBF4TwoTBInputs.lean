module

public import CFSG.LocalAnalysis.StandardType.GGTableBF4TwoTBTorus

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Blueprint.Chevalley TableB TableBSymp Matrix

namespace TableBF4TwoTB

section Inputs


@[expose] def GGF4TwoNonToralSolv (K : Type) [Field K] [CharP K 2] : Prop :=
  ∀ E : Subgroup (adjointGroup .F4 K), IsElemAbelian 3 E → 3 ^ 3 ≤ Nat.card E →
    (∀ g : adjointGroup .F4 K, g ^ 3 = 1 → (∀ e ∈ E, g * e = e * g) → g ∈ E) →
    (¬ ∃ c : adjointGroup .F4 K, E = (tE K).range.map (MulAut.conj c).toMonoidHom) →
      ∀ e ∈ E, e ≠ 1 → Group.IsSolvable (Subgroup.centralizer ({e} : Set (adjointGroup .F4 K)))

@[expose] def GGF4TwoNormIsometry (K : Type) [Field K] [CharP K 2] : Prop :=
  ∀ g : adjointGroup .F4 K, (∀ x ∈ (tE K).range, g * x * g⁻¹ ∈ (tE K).range) →
    ∃ M : (Fin 4 → ZMod 3) →+ (Fin 4 → ZMod 3),
      (∀ v, g * tE K (Multiplicative.ofAdd v) * g⁻¹ = tE K (Multiplicative.ofAdd (M v))) ∧
        ∀ v w, M v ⬝ᵥ M w = v ⬝ᵥ w

@[expose] def GGF4TwoNonToralSolvInput : Prop :=
  ∀ (K : Type) [Field K] [Finite K] [CharP K 2], Nat.card K = 2 → GGF4TwoNonToralSolv K

@[expose] def GGF4TwoNormIsometryInput : Prop :=
  ∀ (K : Type) [Field K] [Finite K] [CharP K 2], Nat.card K = 2 → GGF4TwoNormIsometry K

end Inputs

end TableBF4TwoTB

end CFSG.StandardType

end
