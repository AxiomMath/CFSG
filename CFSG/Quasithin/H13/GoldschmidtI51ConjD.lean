module

public import CFSG.Quasithin.H13.GoldschmidtI51Conj

public section

namespace CFSG.Quasithin.H13.I51

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.H13.A6

variable {G : Type} [Group G]

@[expose] noncomputable def cjEquiv (g : G) (L : Subgroup G) : ↥L ≃* ↥(cj g L) :=
  (MulAut.conj g).subgroupMap L

theorem relIndex_cj (g : G) (H K : Subgroup G) : (cj g H).relIndex (cj g K) = H.relIndex K :=
  Subgroup.relIndex_map_map_of_injective H K (MulAut.conj g).injective

theorem card_cj (g : G) (H : Subgroup G) : Nat.card ↥(cj g H) = Nat.card ↥H :=
  (Nat.card_congr (cjEquiv g H).toEquiv).symm

end CFSG.Quasithin.H13.I51
