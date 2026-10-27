module

public import CFSG.Sporadic.SmallOddCore.J3Data

public section

namespace CFSG.Sporadic.SmallOddCore

open Subgroup CFSG.Sporadic.Th.Native CFSG.Sporadic.SmallOddCore.Native CFSG.Sporadic.Schreier

@[expose] def j3StabFact : Prop := ∀ x : Fin 6156, x ≠ 0 → ∃ s ∈ j3P, s 0 = 0 ∧ s x ≠ x

@[expose] def j3CentConcl : Prop :=
    (tp 6156 j3OuterTbl) ^ 2 = 1 ∧ tp 6156 j3OuterTbl ≠ 1 ∧ tp 6156 j3OuterTbl ∉ j3P ∧
      j3P.map (MulAut.conj (tp 6156 j3OuterTbl)).toMonoidHom = j3P ∧
      (∀ x, x ∈ j3P ⊔ zpowers (tp 6156 j3OuterTbl) ↔ x ∈ j3P ∨ x * tp 6156 j3OuterTbl ∈ j3P) ∧
      Nat.card ↥(j3P ⊔ zpowers (tp 6156 j3OuterTbl)) = 2 * 50232960 ∧
      closure (tp 6156 '' {x | x ∈ j3SylowGenTbls.toArray}) ≤ j3P ⊔ zpowers (tp 6156 j3OuterTbl) ∧
      Nat.card ↥(closure (tp 6156 '' {x | x ∈ j3SylowGenTbls.toArray})) = j3SylowOrder ∧
      (∀ r ∈ j3Rows, tp 6156 r.rep ∈ j3P ⊔ zpowers (tp 6156 j3OuterTbl) ∧
        orderOf (tp 6156 r.rep) = 2 ∧ (r.outer = true ↔ tp 6156 r.rep ∉ j3P) ∧
        closure (tp 6156 '' {x | x ∈ r.centGens.toArray}) =
          j3P ⊓ centralizer ({tp 6156 r.rep} : Set _) ∧
        Nat.card ↥(j3P ⊓ centralizer ({tp 6156 r.rep} : Set (Equiv.Perm (Fin 6156)))) =
          r.centOrder ∧
        (conjClass j3P (tp 6156 r.rep)).ncard = r.classSize ∧
        CFSG.oddCore ↥(j3P ⊓ centralizer ({tp 6156 r.rep} : Set (Equiv.Perm (Fin 6156)))) = ⊥) ∧
      (∀ t ∈ j3P ⊔ zpowers (tp 6156 j3OuterTbl), orderOf t = 2 →
        ∃ r ∈ j3Rows, ∃ g ∈ j3P, t = g * tp 6156 r.rep * g⁻¹) ∧
      (∀ t ∈ j3P ⊔ zpowers (tp 6156 j3OuterTbl), orderOf t = 2 →
        CFSG.oddCore ↥(j3P ⊓ centralizer ({t} : Set (Equiv.Perm (Fin 6156)))) = ⊥)

@[expose] def j3FiveWit : Prop :=
  ∃ x ∈ j3P ⊓ centralizer ({tp 6156 (j3CentTbl 9)} : Set (Equiv.Perm (Fin 6156))),
    orderOf x = 5 ∧ ∃ y ∈ j3P ⊓ centralizer ({tp 6156 (j3CentTbl 9)} : Set (Equiv.Perm (Fin 6156))),
      orderOf (x * (y * x * y⁻¹)) = 6

@[expose] def j3CentFacts : Prop := j3StabFact ∧ j3CentConcl ∧ j3FiveWit

end CFSG.Sporadic.SmallOddCore
