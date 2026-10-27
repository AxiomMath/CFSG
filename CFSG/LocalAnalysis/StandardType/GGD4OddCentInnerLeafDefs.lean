module

public import CFSG.LocalAnalysis.StandardType.GGD4OddCentInnerDefs

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.StandardType.Triality

namespace D4Inner

variable {K : Type} [Field K] [Finite K] [CharP K 2]

noncomputable abbrev centDer (s : Om8 K) : Subgroup (Om8 K) :=
  ⁅Subgroup.centralizer ({s} : Set (Om8 K)), Subgroup.centralizer ({s} : Set (Om8 K))⁆

@[expose] def InnDiagOn (A : Subgroup (MulAut (Om8 K))) (s : Om8 K) (J : Subgroup (Om8 K)) :
    Prop :=
  ∀ a ∈ A, ∃ u ∈ Subgroup.centralizer ({s} : Set (Om8 K)), ∀ j ∈ J, a j = u * j * u⁻¹

@[expose] def ToralOn (A : Subgroup (MulAut (Om8 K))) (s : Om8 K) (J : Subgroup (Om8 K)) : Prop :=
  ∃ D V : Subgroup (Om8 K), D ≤ J ∧
    (∀ x ∈ Subgroup.centralizer (D : Set (Om8 K)), ∀ y ∈ Subgroup.centralizer (D : Set (Om8 K)),
      x * y = y * x) ∧
    (∀ x : Om8 K, x ∈ V ↔ x ∈ Subgroup.centralizer (D : Set (Om8 K)) ∧ x ^ 3 = 1) ∧
    Nat.card V = 3 ^ 4 ∧ Nat.card ↥(V ⊓ D) = 3 ^ 2 ∧
    Nat.card ↥(V ⊓ Subgroup.centralizer (J : Set (Om8 K))) = 3 ^ 2 ∧
    V ⊓ D ⊓ Subgroup.centralizer (J : Set (Om8 K)) = Subgroup.zpowers s ∧
    ∀ a ∈ A, ∃ u ∈ V, ∀ j ∈ J, a j = u * j * u⁻¹

end D4Inner

end CFSG.StandardType

end
