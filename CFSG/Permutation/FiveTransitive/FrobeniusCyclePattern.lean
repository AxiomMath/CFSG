module

public import CFSG.Permutation.FiveTransitive.FrobeniusTransporterCount
public import Mathlib.GroupTheory.GroupAction.MultipleTransitivity

public section

namespace CFSG

namespace FiveTransitive.FrobeniusCyclePattern

open MulAction Equiv
open scoped BigOperators

variable {G X : Type*} [Group G] [MulAction G X] {k : ℕ}

@[expose] def transform (π : Perm (Fin k)) (e : Fin k ↪ X) : Fin k ↪ X :=
  π.toEmbedding.trans e

theorem transform_smul (π : Perm (Fin k)) (g : G) (e : Fin k ↪ X) :
    transform π (g • e) = g • transform π e := rfl

@[expose] def admissible (π : Perm (Fin k)) : SubMulAction G (Fin k ↪ X) :=
  FrobeniusTransporterCount.admissible (transform π) (transform_smul π)

theorem mem_admissible_iff (π : Perm (Fin k)) (e : Fin k ↪ X) :
    e ∈ admissible (G := G) π ↔ ∃ g : G, ∀ i, g • e i = e (π i) := by
  change (∃ g : G, g • e = transform π e) ↔ _
  simp only [Function.Embedding.ext_iff]
  rfl

theorem sum_card_pattern_eq_orbits [Fintype G] [Fintype X]
    (π : Perm (Fin k)) :
    (∑ g : G, Nat.card {e : Fin k ↪ X // ∀ i, g • e i = e (π i)}) =
      Nat.card G * Nat.card (orbitRel.Quotient G (admissible (G := G) (X := X) π)) := by
  classical
  have hpred (g : G) (e : Fin k ↪ X) :
      g • e = transform π e ↔ ∀ i, g • e i = e (π i) := by
    simp only [Function.Embedding.ext_iff]
    rfl
  have he (g : G) : Nat.card {e : Fin k ↪ X // g • e = transform π e} =
      Nat.card {e : Fin k ↪ X // ∀ i, g • e i = e (π i)} :=
    Nat.card_congr (Equiv.subtypeEquivRight (hpred g))
  have h := FrobeniusTransporterCount.sum_card_transporter_eq
    (G := G) (transform (X := X) π) (transform_smul π)
  convert h using 1
  · exact Finset.sum_congr rfl (fun g _ => (he g).symm)
  · congr 2

theorem sum_card_pattern_eq_card_group [Fintype G] [Fintype X]
    (hk : IsMultiplyPretransitive G X k) (hn : k ≤ Fintype.card X)
    (π : Perm (Fin k)) :
    (∑ g : G, Nat.card {e : Fin k ↪ X // ∀ i, g • e i = e (π i)}) = Nat.card G := by
  classical
  let _ : IsPretransitive G (Fin k ↪ X) := hk
  let _ : Nonempty (Fin k ↪ X) := Function.Embedding.nonempty_of_card_le (by simpa using hn)
  have hpred (g : G) (e : Fin k ↪ X) :
      g • e = transform π e ↔ ∀ i, g • e i = e (π i) := by
    simp only [Function.Embedding.ext_iff]
    rfl
  have he (g : G) : Nat.card {e : Fin k ↪ X // g • e = transform π e} =
      Nat.card {e : Fin k ↪ X // ∀ i, g • e i = e (π i)} :=
    Nat.card_congr (Equiv.subtypeEquivRight (hpred g))
  have h := FrobeniusTransporterCount.sum_card_transporter_eq_card_group
    (G := G) (transform (X := X) π) (transform_smul π)
  simpa only [he] using h

end FiveTransitive.FrobeniusCyclePattern

end CFSG
