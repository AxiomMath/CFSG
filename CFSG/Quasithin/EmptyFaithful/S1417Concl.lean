module

public import CFSG.Quasithin.EmptyFaithful.S141Statements

public section

namespace CFSG.Quasithin

open CFSG.Open

variable {G : Type*} [Group G]

@[expose] def Lemma1417CaseTwoCore (T M V : Subgroup G) (R : Prop) : Prop :=
  IsOFourPlusAction M V ∧
    ∃ Y₁ Y₂ : Subgroup G, ∃ t : Subgroup.normalizer (V : Set G),
      Y₁ ≤ M ∧ Y₂ ≤ M ∧ (t : G) ∈ M ∧
      Nonempty (autOn Y₁ V ≃* Equiv.Perm (Fin 3)) ∧ Nonempty (autOn Y₂ V ≃* Equiv.Perm (Fin 3)) ∧
      autOn Y₁ V ⊓ autOn Y₂ V = ⊥ ∧
      (∀ a ∈ autOn Y₁ V, ∀ b ∈ autOn Y₂ V, a * b = b * a) ∧
      conjAct V t ^ 2 = 1 ∧ conjAct V t ≠ 1 ∧
      (autOn Y₁ V).map (MulAut.conj (conjAct V t)).toMonoidHom = autOn Y₂ V ∧
      autOn M V = (autOn Y₁ V ⊔ autOn Y₂ V) ⊔ Subgroup.zpowers (conjAct V t) ∧
      autOn (thompsonJ M) V = autOn Y₁ V ⊔ autOn Y₂ V ∧
      ⁅V, Y₁⁆ ⊓ ⁅V, Y₂⁆ = ⊥ ∧ ⁅V, Y₁⁆ ⊔ ⁅V, Y₂⁆ = V ∧
      Nat.card (⁅V, Y₁⁆ : Subgroup G) = 4 ∧ Nat.card (⁅V, Y₂⁆ : Subgroup G) = 4 ∧
      Nat.card (omegaOneCenterOf (thompsonJ T) ⊓ V : Subgroup G) = 4 ∧ R

theorem lemma1417CaseTwo_iff (T M V : Subgroup G) :
    Lemma1417CaseTwo T M V ↔ Lemma1417CaseTwoCore T M V
      (quasithinOmegaOneCenter T ≤ omegaOneCenterOf (thompsonJ T) ⊓ V ∧
        Nat.card (quasithinOmegaOneCenter T) = 2) :=
  Iff.rfl

@[expose] def CoreConcl (T M V : Subgroup G) (R : Prop) : Prop :=
  ((Nat.card V = 4 ∧ autOn M V = ⊤ ∧
      Nat.card (omegaOneCenterOf (thompsonJ T) ⊓ V : Subgroup G) = 2) ∨
    Lemma1417CaseTwoCore T M V R) ∧
  Nat.card (V ⊓ Subgroup.centralizer (T : Set G) : Subgroup G) ≤ 2 ∧
  ∀ v : V, (v : G) ∈ Subgroup.centralizer (T : Set G) → v ≠ 1 →
    ∀ g ∈ autOn M V, Odd (orderOf g) → g v = v → g = 1

end CFSG.Quasithin
