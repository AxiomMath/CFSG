module

public import Mathlib.SetTheory.Cardinal.NatCard
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.RepresentationTheory.Basic
public import CFSG.ThirdParty.QiuzhenCFSG.Theory.Representation.Maschke

namespace CFSG
end CFSG
open CFSG

/-!
# Complete reducibility for finite-group representations
-/

set_option backward.isDefEq.respectTransparency false in
/-- A representation is completely reducible when its associated `F[G]`-module is semisimple. -/
@[expose] public def Representation.IsCompletelyReducible
    {F G V : Type*} [Field F] [Group G] [AddCommGroup V] [Module F V]
    (ρ : Representation F G V) : Prop :=
  IsSemisimpleModule (MonoidAlgebra F G) ρ.asModule

set_option backward.isDefEq.respectTransparency false in
/-- A finite-group representation is completely reducible when `ringChar F = 0` or
`ringChar F` is prime and coprime to `|G|`. -/
public theorem Representation.isCompletelyReducible_of_ringChar_eq_zero_or_prime_coprime
    {G : Type*} [Group G] [Finite G] {F : Type*} [Field F] {V : Type*}
    [AddCommGroup V] [Module F V] (ρ : Representation F G V)
    (hchar : ringChar F = 0 ∨ (Nat.Prime (ringChar F) ∧ Nat.Coprime (ringChar F) (Nat.card G))) :
    ρ.IsCompletelyReducible := by
  letI : Fintype G := Fintype.ofFinite G
  have hne_card : (Fintype.card G : F) ≠ 0 := by
    intro hcard0
    have hdiv : ringChar F ∣ Fintype.card G := (ringChar.spec F (Fintype.card G)).1 hcard0
    rcases hchar with hchar0 | ⟨hprime, hcop⟩
    · rw [hchar0, Nat.zero_dvd] at hdiv
      exact (Nat.ne_of_gt Fintype.card_pos) hdiv
    · have hdiv1 : ringChar F ∣ 1 := by
        have hcop' : Nat.Coprime (ringChar F) (Fintype.card G) := by
          simpa using hcop
        exact Nat.Coprime.dvd_of_dvd_mul_right (k := ringChar F) (n := Fintype.card G) (m := 1)
          hcop' (by simpa [one_mul] using hdiv)
      exact hprime.not_dvd_one hdiv1
  letI : NeZero (Fintype.card G : F) := ⟨hne_card⟩
  exact MonoidAlgebra.Submodule.instIsSemisimpleModule'
