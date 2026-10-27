module

public import CFSG.Quasithin.H13.A5Facts1321

public section

namespace CFSG.Quasithin.H13.A5

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Assembly.LowTwoRank

@[expose] def FactOutRows1321 : Prop :=
  ∀ (V : Type) [CommGroup V] [Finite V], (∀ w : V, w ^ 2 = 1) →
    ∀ (G L A : Subgroup (MulAut V)), B4Hyp G L → Rows1321Remaining G L A →
      ∀ α : MulAut ↥L, α ^ 3 = 1 → ∃ l : ↥L, α = MulAut.conj l

end CFSG.Quasithin.H13.A5
