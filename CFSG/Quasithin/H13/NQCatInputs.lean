module

public import CFSG.LocalAnalysis.ComponentInitial.SymplecticFlagData

public section

namespace CFSG.Quasithin.H13.NQCat

open CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag

@[expose] def EvenSymplecticThreeFreeSylowOvergroupsTriangular : Prop :=
  ∀ (K : Type) [Field K] [Finite K] [CharP K 2] (r : ℕ), 1 ≤ r →
    (∀ H : Subgroup (StatedSp r K), unipotent r K ≤ H → ¬ 3 ∣ Nat.card H →
      H ≤ borelSubgroup r K) ∧
    Subgroup.normalizer (unipotent r K : Set (StatedSp r K)) = borelSubgroup r K

end CFSG.Quasithin.H13.NQCat
