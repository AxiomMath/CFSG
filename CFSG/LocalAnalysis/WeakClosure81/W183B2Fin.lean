module

public import CFSG.LocalAnalysis.WeakClosure81.W183B2Defs
public import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch5Defs
public import CFSG.Quasithin.EmptyFaithful.S1422Basic

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open Subgroup
open CFSG.LocalAnalysis.UniquenessCase.UC22 (IsL3 IsAlt IsSp4)

@[expose] def invGen {G : Type*} [Group G] (P : Subgroup G) : Subgroup G :=
  Subgroup.closure {t : G | t ∈ P ∧ t * t = 1}

@[expose] def autConj {M : Type} [Group M] (g : MulAut M) (A : Subgroup (MulAut M)) :
    Subgroup (MulAut M) :=
  A.map (MulAut.conj g).toMonoidHom

@[expose] def autNoDynkin (M : Type) [Group M] : Subgroup (MulAut M) :=
  Subgroup.closure {φ : MulAut M | ¬ ActsOnDynkinMod ⊥ (innAutOf M) φ}

@[expose] def Br2NormalConj (M : Type) [Group M] (X₀ : Subgroup (MulAut M)) : Prop :=
  ∀ P₀ : Subgroup (MulAut M), IsSylowIn 2 P₀ X₀ →
    ∀ A : Subgroup (MulAut M), A ≤ X₀ → IsElemAbelian 2 A → 8 ≤ Nat.card A →
      ∃ g ∈ innAutOf M, autConj g A ≤ P₀ ∧
        P₀ ≤ Subgroup.normalizer (autConj g A : Set (MulAut M))

@[expose] def Br2DynkinMoves (M : Type) [Group M] (X₀ : Subgroup (MulAut M)) : Prop :=
  ∀ P₀ : Subgroup (MulAut M), IsSylowIn 2 P₀ X₀ →
    ∀ A : Subgroup (MulAut M), A ≤ P₀ → IsElemAbelian 2 A → 8 ≤ Nat.card A →
      P₀ ≤ Subgroup.normalizer (A : Set (MulAut M)) →
        ∀ τ ∈ Subgroup.normalizer (P₀ : Set (MulAut M)), ActsOnDynkinMod ⊥ (innAutOf M) τ →
          τ ∉ Subgroup.normalizer (A : Set (MulAut M))

@[expose] def FinG4L34 : Prop :=
  ∀ (M : Type) [Group M], IsL3 M 2 →
    Br2NormalConj M (innAutOf M) ∧ Br2DynkinMoves M (innAutOf M)

@[expose] def FinG4A6 : Prop :=
  ∀ (M : Type) [Group M], IsAlt M 6 → (autNoDynkin M).Normal ∧
    (∀ A : Subgroup (MulAut M), IsElemAbelian 2 A → 8 ≤ Nat.card A → A ≤ autNoDynkin M) ∧
    (∀ A : Subgroup (MulAut M), IsElemAbelian 2 A → 8 ≤ Nat.card A →
      innAutOf M ⊔ A = autNoDynkin M) ∧
    Br2NormalConj M (autNoDynkin M) ∧ Br2DynkinMoves M (autNoDynkin M)

@[expose] def AbsIrrOverF4 (X : Type) [Group X] : Prop :=
  ∀ (n : ℕ) (ρ : X →* Matrix.GeneralLinearGroup (Fin n) (AlgebraicClosure (ZMod 2))),
    (∀ W : Submodule (AlgebraicClosure (ZMod 2)) (Fin n → AlgebraicClosure (ZMod 2)),
      (∀ x : X, ∀ w ∈ W, (ρ x : Matrix (Fin n) (Fin n) (AlgebraicClosure (ZMod 2))).mulVec w ∈ W) →
        W = ⊥ ∨ W = ⊤) →
    ∃ (F : Subfield (AlgebraicClosure (ZMod 2)))
      (P : Matrix.GeneralLinearGroup (Fin n) (AlgebraicClosure (ZMod 2))),
      Finite F ∧ Nat.card F ≤ 4 ∧ ∀ x : X, ∀ i j,
        ((P * ρ x * P⁻¹ : Matrix.GeneralLinearGroup (Fin n) (AlgebraicClosure (ZMod 2))) :
          Matrix (Fin n) (Fin n) (AlgebraicClosure (ZMod 2))) i j ∈ F

@[expose] def FinG11Models : Prop :=
  (∀ (M : Type) [Group M], IsL3 M 2 → AbsIrrOverF4 M) ∧
  (∀ (M : Type) [Group M], IsAlt M 6 → AbsIrrOverF4 M) ∧
  (∀ (M : Type) [Group M], IsSp4 M 2 → AbsIrrOverF4 M)

@[expose] def FinSp44Noncyclic5 : Prop :=
  ∀ (M : Type) [Group M], IsSp4 M 2 → ∃ P : Subgroup M, IsPGroup 5 P ∧ ¬ IsCyclic ↥P

@[expose] def Br2TwoRadicals (M : Type) [Group M] (S Q₁ Q₂ : Subgroup (MulAut M)) : Prop :=
  Q₁ ≤ S ∧ Q₂ ≤ S ∧ S ≤ Q₁ ⊔ Q₂ ∧ S ≤ Subgroup.normalizer (Q₁ : Set (MulAut M)) ∧
    S ≤ Subgroup.normalizer (Q₂ : Set (MulAut M)) ∧ IsElemAbelian 2 Q₁ ∧ IsElemAbelian 2 Q₂ ∧
    (∀ x ∈ Q₁ ⊓ Q₂, ∀ s ∈ S, x * s = s * x) ∧
    (∀ E : Subgroup (MulAut M), E ≤ S → IsElemAbelian 2 E → E ≤ Q₁ ∨ E ≤ Q₂) ∧
    (∀ E : Subgroup (MulAut M), E ≤ Q₁ → mOfG E (E ⊓ Q₂) ≤ 2) ∧
    (∀ E : Subgroup (MulAut M), E ≤ Q₂ → mOfG E (E ⊓ Q₁) ≤ 2) ∧
    (⨆ p ∈ innAutOf M ⊓ Subgroup.normalizer (Q₁ : Set (MulAut M)), autConj p S) ⊔
      (⨆ p ∈ innAutOf M ⊓ Subgroup.normalizer (Q₂ : Set (MulAut M)), autConj p S) =
        innAutOf M ∧
    (∀ E : Subgroup (MulAut M), E ≤ Q₁ → 8 ≤ Nat.card E → ¬ E ≤ Q₁ ⊓ Q₂ →
      (⨆ p ∈ innAutOf M ⊓ Subgroup.normalizer (Q₁ : Set (MulAut M)), autConj p E) = Q₁) ∧
    (∀ E : Subgroup (MulAut M), E ≤ Q₂ → 8 ≤ Nat.card E → ¬ E ≤ Q₁ ⊓ Q₂ →
      (⨆ p ∈ innAutOf M ⊓ Subgroup.normalizer (Q₂ : Set (MulAut M)), autConj p E) = Q₂) ∧
    (∀ τ ∈ Subgroup.normalizer (S : Set (MulAut M)), ActsOnDynkinMod ⊥ (innAutOf M) τ →
      autConj τ Q₁ = Q₂ ∧ autConj τ Q₂ = Q₁)

@[expose] def FinG45Sp44 : Prop :=
  ∀ (M : Type) [Group M], IsSp4 M 2 →
    (∀ τ : MulAut M, ActsOnDynkinMod ⊥ (innAutOf M) τ → innAutOf M ⊔ Subgroup.zpowers τ = ⊤) ∧
    ∀ P : Subgroup (MulAut M), IsSylowIn 2 P ⊤ →
      ∃ Q₁ Q₂ : Subgroup (MulAut M), Br2TwoRadicals M (P ⊓ innAutOf M) Q₁ Q₂ ∧
        ∀ A : Subgroup (MulAut M), IsElemAbelian 2 A → 8 ≤ Nat.card A →
          (∃ y : MulAut M, PairViolation A y) ∨
          (∃ g : MulAut M, autConj g A ≤ P ∧
            invGen P ≤ Subgroup.normalizer (autConj g A : Set (MulAut M)) ∧
            ¬ Subgroup.normalizer ((P ⊓ innAutOf M : Subgroup (MulAut M)) : Set (MulAut M)) ≤
              Subgroup.normalizer (autConj g A : Set (MulAut M))) ∨
          (A ≤ innAutOf M ∧ ∃ g : MulAut M, autConj g A ≤ P ⊓ innAutOf M ∧
            ¬ autConj g A ≤ Q₁ ⊓ Q₂)

end CFSG.LocalAnalysis.WeakClosure81

end
