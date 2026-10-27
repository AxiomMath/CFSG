module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.RankThree.PartTwo.KFacts.KS44OutSz
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.RankThree.PartTwo.Sec14.Ronan1422S

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo
open CFSG.Assembly.RankThreeEven (projSp)

@[expose] def IsS6Type (K : Type*) [Group K] (α : MulAut K) : Prop :=
  ∃ ψ : K ≃* alternatingGroup (Fin 6), ∃ σ : Equiv.Perm (Fin 6),
    ∀ k : K, ((ψ (α k) : alternatingGroup (Fin 6)) : Equiv.Perm (Fin 6)) =
      σ * ((ψ k : alternatingGroup (Fin 6)) : Equiv.Perm (Fin 6)) * σ⁻¹

@[expose] def KF1422AutA6 : Prop :=
  (∀ B : Subgroup (alternatingGroup (Fin 6)), Nat.card B = 9 →
      ∀ α : MulAut (alternatingGroup (Fin 6)), (∀ b ∈ B, α b = b) →
        ∃ b ∈ B, α = MulAut.conj b) ∧
    (∀ B : Subgroup (alternatingGroup (Fin 6)), Nat.card B = 9 →
      ∀ Q : Subgroup (MulAut (alternatingGroup (Fin 6))), IsPGroup 2 Q →
        (∀ b ∈ B, ∀ q ∈ Q, MulAut.conj b * q * (MulAut.conj b)⁻¹ ∈ Q) → Q = ⊥) ∧
    (∀ B : Subgroup (alternatingGroup (Fin 6)), Nat.card B = 9 →
      Nat.card (Subgroup.normalizer (B : Set (alternatingGroup (Fin 6)))) = 36) ∧
    ∀ B : Subgroup (alternatingGroup (Fin 6)), Nat.card B = 9 →
      ∃ g : alternatingGroup (Fin 6), ∀ b ∈ B, g * b * g⁻¹ = b⁻¹

@[expose] def KF1422A9Sp6 : Prop :=
  ∀ (S : Type) [Group S] [Finite S],
    (Nonempty (S ≃* alternatingGroup (Fin 9)) ∨ Nonempty (S ≃* projSp 3 (GaloisField 2 1))) →
    (∀ α : MulAut S, α ^ 3 = 1 → ∃ s : S, α = MulAut.conj s) ∧
    ∀ E : Subgroup S, CFSG.Assembly.IsElemAbelian 3 E → Nat.card E = 27 →
    ∀ D : Subgroup S, D ≤ E → Nat.card D = 9 →
      ∃ n ∈ Subgroup.normalizer (E : Set S), D.map (MulAut.conj n).toMonoidHom ≠ D

@[expose] def KF1422J3 : Prop :=
  ∀ (S : Type) [Group S] [Finite S], Nonempty (S ≃* CFSG.Blueprint.NativeSporadic.J3) →
    Nat.card S = 50232960 ∧ (∀ α : MulAut S, α ^ 3 = 1 → ∃ s : S, α = MulAut.conj s) ∧
    ∀ E : Subgroup S, CFSG.Assembly.IsElemAbelian 3 E → Nat.card E = 27 →
    ∀ c ∈ E, c ≠ 1 → ∀ K : Subgroup S, K ≤ Subgroup.centralizer ({c} : Set S) →
      Subgroup.centralizer ({c} : Set S) ≤ Subgroup.normalizer (K : Set S) →
      Nonempty (↥K ≃* alternatingGroup (Fin 6)) → Nat.card (E ⊓ K : Subgroup S) = 9 →
        ∃ t : S, ∃ ht : t ∈ Subgroup.normalizer (K : Set S),
          t ∈ Subgroup.normalizer (E : Set S) ∧
          t ∈ Subgroup.normalizer (Subgroup.zpowers c : Set S) ∧
          ¬ IsS6Type ↥K (K.normalizerMonoidHom ⟨t, ht⟩)

@[expose] def KF1422GL42 : Prop :=
  ∀ (G₀ : Type) [Group G₀] (V : Subgroup G₀), CFSG.Assembly.IsElemAbelian 2 V →
    Nat.card V = 16 → ∀ Y : Subgroup (MulAut ↥V), Nonempty (↥Y ≃* alternatingGroup (Fin 6)) →
      ∀ (g : MulAut ↥V) (hg : g ∈ Subgroup.normalizer (Y : Set (MulAut ↥V))),
        IsS6Type ↥Y (Y.normalizerMonoidHom ⟨g, hg⟩)

@[expose] def KF1422Sp48 : Prop :=
  (∀ (S : Type) [Group S] [Finite S], Nonempty (S ≃* projSp 2 (GaloisField 2 3)) →
      ∀ E : Subgroup S, CFSG.Assembly.IsElemAbelian 3 E → Nat.card E ≠ 27) ∧
    (∀ (Y : Type) [Group Y] [Finite Y] (J : Subgroup Y), J.Normal →
      Nonempty (↥J ≃* projSp 2 (GaloisField 2 3)) →
      Subgroup.centralizer (J : Set Y) = ⊥ → Nat.card Y = 3 * Nat.card J →
      ∀ E : Subgroup Y, CFSG.Assembly.IsElemAbelian 3 E → Nat.card E = 27 →
      Nat.card (E ⊓ J : Subgroup Y) = 9 →
      ∀ P : Subgroup Y, IsPGroup 3 P → E ≤ P → Nat.card P = 243 →
        IsMulCommutative ↥(P ⊓ J) ∧ (∀ x ∈ P, x ^ 3 = 1 → x ∈ E) ∧
        ∀ x ∈ E, x ∉ J → ∀ y ∈ E, y ∉ J →
          ∃ p ∈ P ⊓ J, Subgroup.zpowers (p * x * p⁻¹) = Subgroup.zpowers y) ∧
    ∀ (S : Type) [Group S] [Finite S], Nonempty (S ≃* projSp 2 (GaloisField 2 3)) →
      ∀ α β : MulAut S, α ^ 3 = 1 → (∀ s : S, α ≠ MulAut.conj s) → β * α * β⁻¹ = α⁻¹ → False

end CFSG.RankThree.PartTwo.Sec14.Ronan1422S
