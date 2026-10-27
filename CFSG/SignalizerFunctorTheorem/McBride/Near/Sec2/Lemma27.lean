module

public import CFSG.SignalizerFunctorTheorem.McBride.Near.Sec2.Lemma27Aux12

public section

open CFSG.Open
open scoped Pointwise

namespace CFSG.SignalizerFunctorTheorem.McBride.Near

variable {Γ : Type*} [Group Γ] [Finite Γ]

@[expose] def IsCharIn (K X : Subgroup Γ) : Prop :=
  K ≤ X ∧ ∀ φ : MulAut ↥X, (K.subgroupOf X).map φ.toMonoidHom = K.subgroupOf X

@[expose] def OutSectionsCyclic (p : ℕ) (X : Subgroup Γ) : Prop :=
  ∀ K L M N : Subgroup Γ, IsCharIn K X → IsCharIn L X → L ≤ K → IsChiefFactorOf K M N →
    L ≤ N → ∀ [(N.subgroupOf M).Normal], ∀ P : Subgroup (MulAut (↥M ⧸ N.subgroupOf M)),
      IsPGroup p P → IsCyclic P

@[expose] def wOf (A B X : Subgroup Γ) : Subgroup Γ :=
  ⨆ (E : Subgroup Γ) (_ : E ≤ A ∧ E ⊓ B = ⊥ ∧ E ⊔ B = A), cenIn X E

namespace Lemma27

omit [Finite Γ] in
theorem isCharIn_self (X : Subgroup Γ) : IsCharIn X X :=
  ⟨le_rfl, fun φ => by
    rw [Subgroup.subgroupOf_self, Subgroup.map_top]
    exact MonoidHom.range_eq_top.mpr φ.surjective⟩

omit [Finite Γ] in
theorem isCharIn_bot (X : Subgroup Γ) : IsCharIn ⊥ X :=
  ⟨bot_le, fun φ => by rw [Subgroup.bot_subgroupOf, Subgroup.map_bot]⟩

omit [Finite Γ] in
theorem chiefCyclic_of_outSectionsCyclic {p : ℕ} {X : Subgroup Γ} (hOut : OutSectionsCyclic p X) :
    ChiefCyclic p X := fun M N hMN _ P hP =>
  hOut X ⊥ M N (isCharIn_self X) (isCharIn_bot X) bot_le hMN bot_le P hP

omit [Finite Γ] in
theorem wOf_eq_wSub (A B X : Subgroup Γ) : wOf A B X = wSub A B X := rfl

end Lemma27

open Lemma27

theorem eq_or_eq_of_chief {p : ℕ} (hp : p.Prime) {A B X : Subgroup Γ} (hA : IsElemAbelian p A)
    (hAX : Admits A X) (hcop : Nat.Coprime p (Nat.card X)) (hOut : OutSectionsCyclic p X)
    (hB : B ≤ A) (hchief : IsChiefFactorOf (X ⊔ A) X ⊥) :
    X = wOf A B X ∨ X = cenIn X B := by
  rcases le_wSub_or_le_cenIn_of_chief hp hA hAX hcop hB hchief
    (chiefCyclic_of_outSectionsCyclic hOut) with h | h
  · exact Or.inl (le_antisymm h (wSub_le A B X))
  · exact Or.inr (le_antisymm h (cenIn_le_left _ _))

theorem mul_eq_of_outSectionsCyclic {p : ℕ} (hp : p.Prime) {A B X : Subgroup Γ}
    (hA : IsElemAbelian p A) (hAX : Admits A X) (hcop : Nat.Coprime p (Nat.card X))
    (hOut : OutSectionsCyclic p X) (hB : B ≤ A) :
    (wOf A B X : Set Γ) * (cenIn X B : Set Γ) = X ∧
      (cenIn X B : Set Γ) * (wOf A B X : Set Γ) = X := by
  obtain ⟨h1, h2⟩ := subset_mul_of_chiefCyclic hp hA hAX hcop hB
    (chiefCyclic_of_outSectionsCyclic hOut)
  refine ⟨Set.Subset.antisymm ?_ h1, Set.Subset.antisymm ?_ h2⟩
  · rintro _ ⟨w, hw, z, hz, rfl⟩
    exact mul_mem (wSub_le A B X hw) (cenIn_le_left _ _ hz)
  · rintro _ ⟨z, hz, w, hw, rfl⟩
    exact mul_mem (cenIn_le_left _ _ hz) (wSub_le A B X hw)

end CFSG.SignalizerFunctorTheorem.McBride.Near
