module

public import CFSG.Open.StatedDefs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

@[expose] def s16ntPolar {ι : Type} {K : Type} [Field K] (Q : (ι → K) → K) (v w : ι → K) : K :=
  Q (v + w) - Q v - Q w

@[expose] def S16ntNormOneGen {ι : Type} {K : Type} [Field K] (Q : (ι → K) → K)
    (S : Set (ι → K)) : Prop :=
  ∀ T : Set (ι → K), S ⊆ T →
    (∀ v ∈ T, ∀ w ∈ T, Q v = 1 → Q w = 1 → s16ntPolar Q v w = 1 → v + w ∈ T) →
      {v | Q v = 1} ⊆ T

end CFSG.LocalAnalysis.UniquenessCase.PartTwo

end
