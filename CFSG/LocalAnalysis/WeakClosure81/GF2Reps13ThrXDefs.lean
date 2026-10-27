module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Basic
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs12d

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.LocalAnalysis.UniquenessCase.PartTwo CFSG.Quasithin CFSG.Open Subgroup
open scoped commutatorElement

variable {W : Type} [CommGroup W]

@[expose] def s13IsoSum (X : Subgroup (MulAut W)) (U₀ : Subgroup W) : Subgroup W :=
  ⨆ (V₁ : Subgroup W) (_ : IsIrrOn X V₁ ⊥ ∧ SecIsoOn X V₁ ⊥ U₀ ⊥), V₁

@[expose] def s13IsoComps (X : Subgroup (MulAut W)) : Set (Subgroup W) :=
  {U | ∃ U₀ : Subgroup W, IsIrrOn X U₀ ⊥ ∧ commSub U₀ X ≠ ⊥ ∧ U = s13IsoSum X U₀}

@[expose] def s13KerOn (X : Subgroup (MulAut W)) (U : Subgroup W) : Subgroup (MulAut W) :=
  X ⊓ centSub U

@[expose] def s13Supp (X L : Subgroup (MulAut W)) : Set (Subgroup W) :=
  {U | U ∈ s13IsoComps X ∧ commSub U L ≠ ⊥}

end CFSG.LocalAnalysis.WeakClosure81
