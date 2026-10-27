module

public import CFSG.Blueprint.NativeSporadic

public section

namespace CFSG.Monster.GMS

open CFSG.Blueprint.NativeSporadic

@[expose] def babyCentOrder : Fin 4 → ℕ :=
  ![2 ^ 38 * 3 ^ 9 * 5 ^ 2 * 7 ^ 2 * 11 * 13 * 17 * 19,
    2 ^ 41 * 3 ^ 6 * 5 ^ 3 * 7 * 11 * 23,
    2 ^ 38 * 3 ^ 5 * 5 ^ 2 * 7,
    2 ^ 27 * 3 ^ 6 * 5 ^ 2 * 7 ^ 2 * 13 * 17]

@[expose] def BabyInv (k : Fin 4) (t : B) : Prop :=
  orderOf t = 2 ∧ Nat.card (Subgroup.centralizer ({t} : Set B)) = babyCentOrder k

@[expose] def BabyTableIII : Prop :=
  (∀ t : B, orderOf t = 2 → ∃ k, BabyInv k t) ∧
    ∀ k s t, BabyInv k s → BabyInv k t → IsConj s t

@[expose] def BabyOrbit (k : Fin 4) (r s : B) : Prop :=
  match k with
  | 0 => BabyInv 1 (r * s)
  | 1 => BabyInv 3 (r * s)
  | 2 => orderOf (r * s) = 3
  | 3 => orderOf (r * s) = 4 ∧ BabyInv 1 ((r * s) ^ 2)

@[expose] def babyOrbitSize : Fin 4 → ℕ := ![3968055, 23113728, 2370830336, 11174042880]

@[expose] def BabyTableIV : Prop :=
  ∀ r : B, BabyInv 0 r →
    (∀ s, BabyInv 0 s → s ≠ r → ∃ k, BabyOrbit k r s) ∧
    (∀ k s s', BabyInv 0 s → BabyInv 0 s' → BabyOrbit k r s → BabyOrbit k r s' →
      ∃ g ∈ Subgroup.centralizer ({r} : Set B), g * s * g⁻¹ = s') ∧
    ∀ k, {s | BabyInv 0 s ∧ BabyOrbit k r s}.ncard = babyOrbitSize k

end CFSG.Monster.GMS
