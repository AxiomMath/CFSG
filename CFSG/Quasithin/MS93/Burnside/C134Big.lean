module

public import CFSG.Quasithin.MS93.ASC134

public section

namespace CFSG.Quasithin.MS93

open CFSG.QuasithinUnique CFSG.Quasithin
open CFSG.Open hiding StatedSL StatedSp
open CFSG.Assembly.LowTwoRank (StatedSL StatedSp)
open scoped Pointwise

@[expose] def burnsideC134w_AS_C_1_34_corrBig : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (G₀ R L : Subgroup G), IsMSPair G₀ R → L ∈ cComp G₀ →
    (G₀ : Set G) = (L : Set G) * (R : Set G) →
    (∃ (n : ℕ) (F : Type) (_ : Field F) (_ : Fintype F) (α : ↥L →* ↥(StatedSL 3 F)),
      2 ≤ n ∧ Fintype.card F = 2 ^ n ∧ IsModO2Surj L α) →
      ∃ i : ℕ, IsC134CaseCorr i G₀ R L

end CFSG.Quasithin.MS93
