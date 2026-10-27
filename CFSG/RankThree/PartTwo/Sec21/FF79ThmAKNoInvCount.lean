module

public import Mathlib.GroupTheory.Perm.Cycle.Type

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF79

theorem card_modEq_five_fixed {V : Type} [Finite V] (S : Set V) (σ : V → V)
    (h5 : ∀ v, σ (σ (σ (σ (σ v)))) = v) (hS : ∀ v ∈ S, σ v ∈ S) :
    Nat.card S ≡ Nat.card {v : V // v ∈ S ∧ σ v = v} [MOD 5] := by
  classical
  haveI := Fintype.ofFinite S
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  let f : Function.End S := fun s => ⟨σ s, hS s s.2⟩
  have hf : f ^ 5 ^ 1 = 1 := by
    funext s
    apply Subtype.ext
    exact h5 s
  have key := Equiv.Perm.card_fixedPoints_modEq hf
  have e : Function.fixedPoints f ≃ {v : V // v ∈ S ∧ σ v = v} :=
    { toFun := fun x => ⟨x.1.1, x.1.2, congrArg Subtype.val x.2⟩
      invFun := fun x => ⟨⟨x.1, x.2.1⟩, Subtype.ext x.2.2⟩
      left_inv := fun x => rfl
      right_inv := fun x => rfl }
  have h1 : Nat.card S = Fintype.card S := Nat.card_eq_fintype_card
  have h2 : Nat.card {v : V // v ∈ S ∧ σ v = v} = Fintype.card (Function.fixedPoints f) := by
    rw [Nat.card_congr e.symm, Nat.card_eq_fintype_card]
  rw [h1, h2]
  exact key

end CFSG.RankThree.PartTwo.Sec21.FF79
