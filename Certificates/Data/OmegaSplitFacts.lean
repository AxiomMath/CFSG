module

public import Certificates.Data.OmegaSplit

public section

namespace Certificates.OmegaSplit

open CFSG.ComponentClassification.CatFactsSmall.PSp43 CFSG.GH74.KGroups

local notation "P45" => Equiv.Perm (Fin 45)

@[expose] def bSet : Set P45 := {g | g ∈ b0Elems ()}

@[expose] def Facts : Prop :=
  ∃ X : Subgroup P45, X ≤ QA45.originalSubgroup ⊓ Subgroup.normalizer bSet ∧
    (∀ x ∈ X, x ∈ bSet → x = 1) ∧
      ∀ a ∈ QA45.originalSubgroup ⊓ Subgroup.normalizer bSet, ∃ x ∈ X, ∃ b ∈ bSet, a = x * b

end Certificates.OmegaSplit
