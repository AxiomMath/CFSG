module

public import CFSG.LocalAnalysis.QuasithinUnique.PushingUp.Blocks

public section

namespace CFSG.Quasithin.F112R.St84

open CFSG.Open CFSG.QuasithinUnique

variable {G : Type*} [Group G]

structure L3qLocalData (L1 L2 S : Subgroup G) (f : ℕ) : Prop where
  card_S : Nat.card S = 2 ^ (3 * f)
  card_left : Nat.card (pCoreOf 2 L1) = 2 ^ (2 * f)
  lin_left : IsLin2Type L1 f
  card_right : Nat.card (pCoreOf 2 L2) = 2 ^ (2 * f)
  lin_right : IsLin2Type L2 f
  card_inf : Nat.card ↥(pCoreOf 2 L1 ⊓ pCoreOf 2 L2) = 2 ^ f

theorem L3qLocalData.symm {L1 L2 S : Subgroup G} {f : ℕ} (h : L3qLocalData L1 L2 S f) :
    L3qLocalData L2 L1 S f :=
  ⟨h.card_S, h.card_right, h.lin_right, h.card_left, h.lin_left, by rw [inf_comm]; exact h.card_inf⟩

@[expose] def cubeDetGL (F : Type*) [Field F] : Subgroup (GL (Fin 2) F) :=
  (powMonoidHom 3 : Fˣ →* Fˣ).range.comap Matrix.GeneralLinearGroup.det

@[expose] def ActsByMatrix {F : Type*} [Field F] {n : ℕ} {Q : Subgroup G}
    (β : ↥Q ≃* Multiplicative (Fin n → F)) (p : G) (A : Matrix (Fin n) (Fin n) F) : Prop :=
  ∀ x y : ↥Q, (y : G) = p * x * p⁻¹ →
    Multiplicative.toAdd (β y) = A.mulVec (Multiplicative.toAdd (β x))

@[expose] def LinAction (P Q : Subgroup G) {F : Type*} [Field F] {n : ℕ}
    (Γ : Subgroup (GL (Fin n) F)) : Prop :=
  ∃ β : ↥Q ≃* Multiplicative (Fin n → F),
    (∀ p ∈ P, ∃ A ∈ Γ, ActsByMatrix β p (A : Matrix (Fin n) (Fin n) F)) ∧
      ∀ A ∈ Γ, ∃ p ∈ P, ActsByMatrix β p (A : Matrix (Fin n) (Fin n) F)

structure IsLinSemidirect (P Q : Subgroup G) {F : Type*} [Field F] {n : ℕ}
    (Γ : Subgroup (GL (Fin n) F)) : Prop where
  le : Q ≤ P
  normal : P ≤ Subgroup.normalizer (Q : Set G)
  cent : P ⊓ Subgroup.centralizer (Q : Set G) ≤ Q
  split : ∃ X : Subgroup G, X ≤ P ∧ X ⊓ Q = ⊥ ∧ Q ⊔ X = P
  act : LinAction P Q Γ

end CFSG.Quasithin.F112R.St84
