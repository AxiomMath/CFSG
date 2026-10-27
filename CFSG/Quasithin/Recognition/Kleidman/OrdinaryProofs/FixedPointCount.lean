module

public import Mathlib.GroupTheory.Perm.Cycle.Type

public section

namespace CFSG.Quasithin.Recognition.Kleidman.OrdinaryProofs

abbrev FixedSet {X : Type*} (σ : Equiv.Perm X) : Type _ := {x : X // σ x = x}

theorem natCard_fixed_modEq_three {X : Type*} [Finite X] (σ : Equiv.Perm X) (hσ : σ ^ 3 = 1) :
    Nat.card X ≡ Nat.card (FixedSet σ) [MOD 3] := by
  classical
  have := Fintype.ofFinite X
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h1 : σ ^ 3 ^ 1 = 1 := by rw [pow_one, hσ]
  have h2 := Equiv.Perm.card_compl_support_modEq h1
  have hc : σ.supportᶜ = Finset.univ.filter (fun x => σ x = x) := by
    ext x
    simp [Equiv.Perm.mem_support]
  have h3 : Nat.card (FixedSet σ) = (Finset.univ.filter (fun x => σ x = x)).card := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  rw [hc] at h2
  rw [Nat.card_eq_fintype_card, h3]
  exact h2.symm

end CFSG.Quasithin.Recognition.Kleidman.OrdinaryProofs

end
