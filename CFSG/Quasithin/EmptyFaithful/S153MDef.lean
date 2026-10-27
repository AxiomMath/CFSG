module

public import CFSG.Quasithin.EmptyFaithful.SzN15Out

public section

namespace CFSG.Quasithin

open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique

namespace S153M

@[expose] def FFNatShape {V : Type} [CommGroup V] (L : Subgroup (MulAut V)) : Prop :=
  (∃ (K : Type) (_ : Field K) (_ : Finite K) (m : ℕ), Nat.card K = 2 ^ m ∧
      (FFModel.nat (StatedSL 2 K)).Realizes L (commV L) (fixV L ⊓ commV L)) ∨ SzN15.NatOutcome L

end S153M

end CFSG.Quasithin
