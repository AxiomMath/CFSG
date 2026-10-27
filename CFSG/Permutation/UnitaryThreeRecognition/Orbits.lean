module

public import Mathlib.GroupTheory.GroupAction.Quotient
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Group.Subgroup.Finite
public import Mathlib.GroupTheory.Coset.Card

public section

namespace CFSG.UnitaryThreeRecognition

open MulAction

theorem card_dvd_card_mul_of_stabilizer_le {H X : Type*} [Group H] [MulAction H X] [Finite H]
    [Finite X] (K : Subgroup H) (hK : ∀ x : X, stabilizer H x ≤ K) :
    Nat.card H ∣ Nat.card K * Nat.card X := by
  classical
  let : Fintype X := Fintype.ofFinite X
  let : Fintype (orbitRel.Quotient H X) := Fintype.ofFinite _
  have hsum : Nat.card X = ∑ ω : orbitRel.Quotient H X, Nat.card ω.orbit := by
    rw [Nat.card_congr (MulAction.selfEquivSigmaOrbits' H X), Nat.card_sigma]
  rw [hsum, Finset.mul_sum]
  apply Finset.dvd_sum
  intro ω _
  obtain ⟨x, rfl⟩ := Quotient.mk''_surjective ω
  have hos := Nat.card_congr (MulAction.orbitProdStabilizerEquivGroup H x)
  rw [Nat.card_prod] at hos
  have hdvd : Nat.card (stabilizer H x) ∣ Nat.card K := Subgroup.card_dvd_of_le (hK x)
  rw [orbitRel.Quotient.orbit_mk, ← hos, mul_comm]
  exact mul_dvd_mul_right hdvd _

theorem card_dvd_of_stabilizer_eq_bot {H X : Type*} [Group H] [MulAction H X] [Finite H]
    [Finite X] (hfree : ∀ x : X, stabilizer H x = ⊥) : Nat.card H ∣ Nat.card X := by
  have := card_dvd_card_mul_of_stabilizer_le (⊥ : Subgroup H) (fun x => (hfree x).le)
  simpa [Subgroup.card_bot] using this

end CFSG.UnitaryThreeRecognition
