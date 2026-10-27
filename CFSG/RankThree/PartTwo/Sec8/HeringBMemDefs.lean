module

public import CFSG.Assembly.RankThreeEvenDefs

public section

namespace CFSG.RankThree.PartTwo.Sec8

open CFSG.Assembly.RankThreeEven (projSp)
open scoped commutatorElement

@[expose] def KF812U3Cent : Prop :=
  ∀ (M : Type) [Group M] [Finite M],
    (Nonempty (M ≃* alternatingGroup (Fin 9)) ∨ Nonempty (M ≃* projSp 3 (GaloisField 2 1))) →
    ∀ (E Q : Subgroup M) (v : M),
      CFSG.Assembly.IsElemAbelian 3 E → Nat.card E = 27 → v ∈ E → v ≠ 1 →
      Q ≤ Subgroup.centralizer ({v} : Set M) → Nat.card Q = 8 →
      (∃ z ∈ Q, z ≠ 1 ∧ ∀ x ∈ Q, x ≠ 1 → x = z ∨ x ^ 2 = z) →
      Nonempty (M ≃* projSp 3 (GaloisField 2 1)) ∧
      ∃ g ∈ Subgroup.normalizer (E : Set M), g * v = v * g ∧ (∃ k : ℕ, g ^ 3 ^ k = 1) ∧
        ∃ e ∈ E, g * e * g⁻¹ ≠ e

@[expose] def KF812U3Irred : Prop :=
  ∀ (M : Type) [Group M] [Finite M], Nonempty (M ≃* projSp 3 (GaloisField 2 1)) →
    ∀ (E S H : Subgroup M) (u g : M),
      CFSG.Assembly.IsElemAbelian 3 E → Nat.card E = 27 → S ≤ E → Nat.card S = 9 → u ∈ E →
      u ∉ S → Group.IsPerfect H → S ≤ H → H ≤ Subgroup.centralizer ({u} : Set M) →
      g ∈ Subgroup.normalizer (E : Set M) → (∃ k : ℕ, g ^ 3 ^ k = 1) → (∃ e ∈ E, g * e * g⁻¹ ≠ e) →
      ∀ U : Subgroup M, U ≤ E →
        (∀ s ∈ Subgroup.normalizer (E : Set M), s * u = u * s →
          s ∈ Subgroup.normalizer (U : Set M)) →
        g ∈ Subgroup.normalizer (U : Set M) → U = ⊥ ∨ U = E

end CFSG.RankThree.PartTwo.Sec8
