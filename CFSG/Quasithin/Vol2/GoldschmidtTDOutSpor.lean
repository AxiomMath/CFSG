module

public import CFSG.Quasithin.H13.NQCatSporadic
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1J4OutFinal
public import CFSG.Quasithin.Vol2.GoldschmidtTDOutAbs

public section

namespace CFSG.Quasithin.H13.OutTwoNilp

open CFSG.Blueprint
open CFSG.ComponentClassification.OuterAutomorphisms (Outer equivalence)
open CFSG.Quasithin.H13.Ch838 (TwoNilpotent)

theorem twoNilpotent_outer_of_sporadic_ne_J4
    {s : TauCeti.SporadicName} (hs : s ∈ CFSG.SectionRank.sqtkSporadicNames) (hJ4 : s ≠ .J4)
    {S : Type} [Group S] [Finite S] (e : S ≃* NativeSporadic.Carrier s) :
    TwoNilpotent (Outer S) := by
  have hle : Nat.card (Outer S) ≤ 4 := by
    rw [Nat.card_congr (equivalence e).toEquiv]
    exact NQCat.card_outer_sqtkSporadic_le_four hs hJ4
  have hc := NQCat.isMulCommutative_of_card_le_four hle
  exact twoNilpotent_of_comm fun a b => hc.is_comm.comm a b

theorem twoNilpotent_outer_of_J4
    {S : Type} [Group S] (e : S ≃* NativeSporadic.Carrier .J4) : TwoNilpotent (Outer S) := by
  have hodd : Odd (Nat.card (Outer S)) := by
    rw [Nat.card_congr (equivalence e).toEquiv]
    exact CFSG.QuasithinUnique.Setup.X1.j4OuterOdd
  exact twoNilpotent_of_odd hodd

end CFSG.Quasithin.H13.OutTwoNilp
