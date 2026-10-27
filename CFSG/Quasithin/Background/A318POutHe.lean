module

public import CFSG.Quasithin.Background.A318POutCheap
public import CFSG.Sporadic.Schreier.PairHePairs

public section

namespace CFSG.Quasithin

open CFSG.Blueprint
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)

namespace A318P

theorem not_dvd_outer_He
    {S : Type} [Group S] [Finite S] (e : S ≃* NativeSporadic.Carrier .He)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) : ¬ p ∣ Nat.card (Outer S) :=
  not_dvd_outer_of_carrier e CFSG.Sporadic.Schreier.AT_He_Schreier.1 hp hp2

end A318P

end CFSG.Quasithin
