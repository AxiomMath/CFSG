module

public import CFSG.Blueprint.NativeSporadic
public import CFSG.Foundations.Basic

public section

namespace CFSG.RankThree.PartTwo.J2Residue

open CFSG CFSG.Blueprint.NativeSporadic

@[expose] def KJFix : Prop :=
  ∀ (L : Type) [Group L] [Finite L], Nonempty (L ⧸ CFSG.pCore 2 L ≃* J2) →
    ∀ M : Subgroup L, M.Normal → M ≤ CFSG.pCore 2 L → M ≠ ⊥ →
      (∀ K : Subgroup L, K.Normal → K ≤ M → K = ⊥ ∨ K = M) →
    ∀ d : L, orderOf d = 3 →
      (∃ S : Sylow 3 L, d ∈ (S : Subgroup L) ∧ (S : Subgroup L) ≤ Subgroup.centralizer {d}) →
      Nat.card ↥(M ⊓ Subgroup.centralizer ({d} : Set L)) = 2 → Nat.card M = 2

@[expose] def KJSplit : Prop :=
  ∀ (L : Type) [Group L] [Finite L] (M : Subgroup L) [M.Normal], IsPGroup 2 M → M ≠ ⊥ →
      (∀ K : Subgroup L, K.Normal → K ≤ M → K = ⊥ ∨ K = M) → Nonempty (L ⧸ M ≃* J2) →
    ∀ d : L, orderOf d = 3 →
      (∃ S : Sylow 3 L, d ∈ (S : Subgroup L) ∧ (S : Subgroup L) ≤ Subgroup.centralizer {d}) →
      M ⊓ Subgroup.centralizer ({d} : Set L) = ⊥ → ∃ H : Subgroup L, Subgroup.IsComplement' H M

@[expose] def KJCover : Prop :=
  ∀ (L : Type) [Group L] [Finite L], Group.IsPerfect L →
    ∀ (Z : Subgroup L) [Z.Normal], Z ≤ Subgroup.center L → Nat.card Z = 2 →
      Nonempty (L ⧸ Z ≃* J2) →
    ∀ d : L, orderOf d = 3 →
      (∃ S : Sylow 3 L, d ∈ (S : Subgroup L) ∧ (S : Subgroup L) ≤ Subgroup.centralizer {d}) →
      Z ⊓ inSubgroup perfectResidual (Subgroup.centralizer ({d} : Set L)) = ⊥

@[expose] def KG1 : Prop :=
  ∀ (d : J2) (S : Subgroup J2), Nat.card S = 27 → d ≠ 1 → d ∈ S →
      S ≤ Subgroup.centralizer {d} →
    (∀ T₁ T₂ : Subgroup J2, Subgroup.zpowers d < T₁ → T₁ < S → Subgroup.zpowers d < T₂ →
      T₂ < S → ∃ n ∈ Subgroup.normalizer (S : Set J2) ⊓
          Subgroup.normalizer (Subgroup.zpowers d : Set J2),
        T₁.map (MulAut.conj n).toMonoidHom = T₂) ∧
    ∃ n ∈ Subgroup.normalizer (S : Set J2) ⊓ Subgroup.normalizer (Subgroup.zpowers d : Set J2),
      ∀ s ∈ S, n * s * n⁻¹ * s ∈ Subgroup.zpowers d

end CFSG.RankThree.PartTwo.J2Residue
