module

public import CFSG.Quasithin.EmptyFaithful.SzF53B3O3Main
public import CFSG.Quasithin.EmptyFaithful.SzF53MSecD

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.F7 CFSG.Quasithin.F53 CFSG.Quasithin.F53Mod
open CFSG.Quasithin.CosetGeom

namespace F53B3

theorem n37_orth_of_C1_S4 {G : Type} [Group G] [Finite G] {H M S : Subgroup G}
    (hB : B3FactsO H M S) (hBl : B3Block H M S) (hC1 : OrthC1 H M S) (hS4 : OrthS4 H M S)
    {β : Geo H M} (hβ : vtype β = false) : ⁅Kq β, oTwoRes (stab β)⁆ ≤ Vn β :=
  n37_orth_of_hM6 hB hBl hC1 hS4
    (fun _ _ _ _ hq hUK hUQ hs hnc _ ha haQ ha2 haA =>
      two_lt_secIdx_of_A5_involution hq hUK hUQ hs hnc ha haQ ha2 haA) hβ

end F53B3

end CFSG.Quasithin
