module

public import CFSG.Monster.GMS.Facts.BabyTables
public import CFSG.Sporadic.Fi22.Transpositions

public section

namespace CFSG.Monster.GMS

open CFSG.Blueprint.NativeSporadic

@[expose] def babyStar (r s : B) : Set B :=
  {t | BabyInv 0 t ∧ BabyInv 1 (r * t) ∧ BabyInv 1 (s * t)}

@[expose] def BabyFi22Slice : Prop :=
  ∀ r s : B, BabyInv 0 r → BabyInv 0 s → orderOf (r * s) = 3 →
    (∃ χ : babyStar r s ≃ CFSG.Sporadic.Fi22.D,
      (∀ t u : babyStar r s,
        (t : B) * u = u * t ↔ ((χ t : CFSG.Sporadic.Fi22.J) * χ u = χ u * χ t)) ∧
      ∀ (t u : babyStar r s) (h : (t : B) * u * t ∈ babyStar r s),
        ((χ ⟨_, h⟩ : CFSG.Sporadic.Fi22.D) : CFSG.Sporadic.Fi22.J) =
          (χ t : CFSG.Sporadic.Fi22.J) * χ u * χ t) ∧
    ∀ g ∈ Subgroup.centralizer ({r} : Set B) ⊓ Subgroup.centralizer {s},
      (∀ t ∈ babyStar r s, g * t = t * g) → g = 1

end CFSG.Monster.GMS
