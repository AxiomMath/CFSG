module

public import CFSG.LocalAnalysis.WeakClosure81.W16PFiveSix
public import CFSG.LocalAnalysis.WeakClosure81.W15SixB
public import CFSG.LocalAnalysis.WeakClosure81.W16Setup

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open Subgroup

variable {G : Type} [Group G] [Finite G]

@[expose] def DFam16 (M H A : Subgroup G) : Set (Subgroup G) :=
  {X | X ≤ H ∧ (∃ P : Subgroup G, IsSylowIn 2 P (kerMOf M H) ∧ P ≤ kerMOf M X) ∧ IsPairAt M X A}

structure Hyp167 (M V₀ V U S H : Subgroup G) (g : G) (X T : Subgroup G) : Prop where
  cex : Cex16 M V₀ V U S
  min : IsMinFam16 M U S H
  le_S : conjSubgroup V g ≤ S
  mem : X ∈ DFam16 M H (conjSubgroup V g)
  min_X : ∀ X' ∈ DFam16 M H (conjSubgroup V g), X' ≤ X → X' = X
  sylow : IsSylowIn 2 T (X ⊓ M)
  A_le_T : conjSubgroup V g ≤ T

end CFSG.LocalAnalysis.WeakClosure81

end
