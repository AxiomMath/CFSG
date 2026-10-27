module

public import CFSG.Quasithin.Vol2.E2SevenKG7Large
public import CFSG.Quasithin.Vol2.E2SevenKG2L2
public import CFSG.Quasithin.Vol2.E2SevenKG2Sz
public import CFSG.Quasithin.Vol2.Ch3E213MG41SZ8
public import CFSG.Quasithin.Vol2.GoldschmidtSp4C2WireBase

public section

namespace CFSG.Quasithin

namespace E2

open CFSG.Open CFSG.QuasithinUnique

@[expose] def E27Sp4One : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (X T M K V : Subgroup G), Hyp28 X T M V →
    kerIn M X = ⊥ → K ≤ X → X ≤ Subgroup.normalizer (K : Set G) →
    X ⊓ Subgroup.centralizer (K : Set G) = ⊥ → K ⊔ T = X → IsSp4Prime 1 ↥K →
    IsDiagramNontrivial T K (T ⊓ K) →
    M ⊓ K = K ⊓ Subgroup.normalizer ((T ⊓ K : Subgroup G) : Set G) → E1.nParam X = 1 →
    4 ≤ Nat.card V → ∃ I : Subgroup G, ASInputs.IsInIHTVC X T M V I

theorem e27Sp4_of_one
    (h1 : E27Sp4One) : E27Sp4 := by
  intro G _ _ X T M K V n h hker hKX hXN hC hKT hn hSp hD hMK hnX hV4
  rcases Nat.lt_or_ge n 2 with hlt | hge
  · obtain rfl : n = 1 := by omega
    exact h1 G X T M K V h hker hKX hXN hC hKT hSp hD hMK (by rw [hnX, Nat.cast_one]) hV4
  · exact exists_isInIHTVC_sp4_two_le kgBenderSubL2_holds kgBenderSubSz_holds
      Ch3E213M.irrStatement_holds Ch3E213M.Sp4C2.factSp4TransvW_holds
      Ch3E213M.factSp4CTwo_holds h hker hKX hXN hC hKT hge hSp hMK hnX hV4

end E2

end CFSG.Quasithin
