module

public import CFSG.RankThree.PartOne.F106.ConvFinite
public import CFSG.RankThree.PartOne.Census3.NativeForm
public import CFSG.RankThree.PartOne.CTP.SporadicOrders
public import CFSG.RankThree.PartOne.CTP.SeitzExcModels
public import CFSG.RankThree.PartOne.SPOR.I613Item3

public section

namespace CFSG.RankThree.PartOne.F106

open CFSG.Assembly.LowTwoRank CFSG.RankThree.PartOne.N143 CFSG.RankThree.PartOne.S12K
open CFSG.RankThree.PartOne.Census3 (ThmThreeItem3 ThmThreeItem5 ThmThreeItem6 sporadicsThm3
  nonempty_carrier_mulEquiv_of_mem)

open CFSG.Blueprint
open TauCeti (SporadicName)


section Certs


theorem card_carrier_eq_sporadicOrder {s : SporadicName} (hs : s ∈ sporadicsThm3) :
    Nat.card (NativeSporadic.Carrier s) = sporadicOrder s := by
  simp only [sporadicsThm3, List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact CFSG.Sporadic.Mathieu.card_M11
  · exact CFSG.Sporadic.Mathieu.card_M12
  · exact CFSG.Sporadic.Mathieu.card_M22
  · exact CFSG.RankThree.PartOne.CTP.card_M23
  · exact CFSG.Sporadic.Mathieu.card_M24
  · exact CFSG.Sporadic.J1.card_J1
  · exact CFSG.Sporadic.J2.card_J2
  · exact CFSG.Sporadic.J3.card_J3
  · exact CFSG.Sporadic.J4.card_J4
  · exact CFSG.Sporadic.McL.card_McL
  · exact CFSG.Sporadic.Ly.card_Ly
  · exact CFSG.Sporadic.HS.card_HS
  · exact CFSG.Sporadic.He.card_He
  · exact CFSG.Sporadic.Suz.card_Suz
  · exact CFSG.Sporadic.Ru.card_Ru
  · exact CFSG.Sporadic.ON.card_ON_eq
  · exact CFSG.Sporadic.Co3.card_Co3
  · exact CFSG.Sporadic.Co2.card_Co2
  · exact CFSG.Sporadic.HN.card_HN
  · exact CFSG.RankThree.PartOne.CTP.card_Th

section Items


theorem finiteListOrder_of_item {X : Type} [Group X] (hsimple : IsSimpleGroup X)
    (h : ThmThreeItem3 X ∨ ThmThreeItem5 X ∨ ThmThreeItem6 X) :
    FiniteListOrder (Nat.card X) := by
  rcases h with h3 | ⟨n, hn5, hn12, ⟨e⟩⟩ | ⟨s, hs, ⟨e⟩⟩
  · left
    rw [CFSG.RankThree.PartOne.SPOR.card_smallRee_model (f := 3) (ℓ := 3) rfl
      (CFSG.RankThree.PartOne.CTP.reeTitsModel_reeG2 1 h3)]
    norm_num
  · right; left
    refine ⟨n, hn5, hn12, ?_⟩
    have : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.mpr (by omega)
    rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup, Nat.card_eq_fintype_card,
      Fintype.card_fin]
  · right; right
    refine ⟨s, hs, ?_⟩
    have : IsSimpleGroup s.Group := e.symm.isSimpleGroup
    obtain ⟨b⟩ := nonempty_carrier_mulEquiv_of_mem hs
    rw [Nat.card_congr (e.trans b.symm).toEquiv]
    exact card_carrier_eq_sporadicOrder hs

theorem smallEvenParams_of_finite_item {X : Type} [Group X] (hsimple : IsSimpleGroup X)
    {t : StatedLieTag} {n f : ℕ} (hadm : StatedLieAdmissible t n 2 f)
    (hcard : Nat.card X = charTwoOrder t n f)
    (h : ThmThreeItem3 X ∨ ThmThreeItem5 X ∨ ThmThreeItem6 X) : SmallEvenParams t n f :=
  smallEvenParams_of_finiteListOrder hadm (hcard ▸ finiteListOrder_of_item hsimple h)

end Items

end Certs

end CFSG.RankThree.PartOne.F106
