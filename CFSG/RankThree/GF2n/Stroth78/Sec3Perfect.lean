module

import CFSG.GroupTheory.PerfectOfClassMul
public import CFSG.RankThree.GF2n.Stroth78.Sec2Defs
public import CFSG.RankThree.OrthogonalInvolutions.Basic

public section

namespace CFSG.RankThree.GF2n.Stroth78

open CFSG CFSG.Open CFSG.RankThree.GF2n.Tim79a CFSG.LargeExtraspecial.Timmesfeld
open CFSG.Timmesfeld
open CFSG.RankThree.OrthogonalInvolutions Module

variable {G : Type} [Group G] [Finite G] {z : G} {E F : Subgroup G}

theorem commutator_Xsub_eq_of_mul_mem (S : Setting z E F) {a : G}
    (hclass : ∀ α ∈ Eset S a, ∀ α' ∈ Eset S a, ∃ x ∈ Xsub S a, α' = x * α * x⁻¹)
    {α β : Hbar z} (hα : α ∈ Eset S a) (hβ : β ∈ Eset S a) (hαβ : α * β ∈ Eset S a) :
    ⁅Xsub S a, Xsub S a⁆ = Xsub S a :=
  CFSG.GroupTheory.commutator_eq_self_of_mul_mem (D := Eset S a) rfl hclass hα hβ hαβ

end CFSG.RankThree.GF2n.Stroth78
