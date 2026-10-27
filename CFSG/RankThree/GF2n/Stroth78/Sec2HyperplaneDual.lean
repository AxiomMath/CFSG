module

public import CFSG.RankThree.GF2n.Stroth78.Sec2SeventeenO2
public import CFSG.RankThree.OrthogonalInvolutions.Basic

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

public section

namespace CFSG.RankThree.GF2n.Stroth78

open CFSG CFSG.Open CFSG.RankThree.GF2n.Tim79a CFSG.LargeExtraspecial.Timmesfeld
open CFSG.RankThree.OrthogonalInvolutions Module
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {z : G} {E F : Subgroup G}

theorem diffSpan_eq_iSup_commSpace (S : Setting z E F) (Y : Subgroup (Hbar z)) :
    diffSpan S Y = ⨆ y : ↥Y,
      commSpace (rhoBar S (y : Hbar z) : Additive (QbarOf S) ≃ₗ[ZMod 2] Additive (QbarOf S)) := by
  apply le_antisymm
  · rw [diffSpan, Submodule.span_le]
    rintro u ⟨y, hy, v, rfl⟩
    exact le_iSup (fun y : ↥Y => commSpace (rhoBar S (y : Hbar z) :
      Additive (QbarOf S) ≃ₗ[ZMod 2] Additive (QbarOf S))) ⟨y, hy⟩
      (sub_mem_commSpace _ v)
  · refine iSup_le fun y => ?_
    intro u hu
    obtain ⟨v, rfl⟩ := mem_commSpace.mp hu
    exact Submodule.subset_span ⟨(y : Hbar z), y.2, v, rfl⟩
