module

public import CFSG.Quasithin.EmptyFaithful.A38c8Main
public import CFSG.Quasithin.EmptyFaithful.A38c8Row
public import CFSG.Quasithin.EmptyFaithful.A38c8L5
public import CFSG.Quasithin.EmptyFaithful.A38c8M24
public import CFSG.Quasithin.EmptyFaithful.A38c8J4

public section

namespace CFSG.Quasithin.A38c8

open CFSG.Open CFSG.QuasithinUnique

theorem l4Rows_of_sporadic
    (hsp : SporadicL4Inner) : L4Rows := by
  intro Y _ _ N T B hN hT hBN hB hTB h4 hcase t ht
  rcases row_of_a312 hBN h4 hcase with h5 | ⟨hext, hM⟩ | hJ
  · exact inner_of_l5 hN hT hBN hB hTB h4 h5 t ht
  · exact inner_of_m24 hsp.1 hN hM hT hBN hext hTB t ht
  · exact inner_of_j4 hsp.2 hN hJ hT hBN hB hTB h4 t ht

theorem input32ThreeComp_of_inputs
    (h11 : StageLemma14111) (h113 : StageLemma14113) (hpre : Input32Preamble)
    (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h39 : A39ForSQTK) (h312 : A312ForSQTK)
    (hsp : SporadicL4Inner) : Input32ThreeComp :=
  input32ThreeComp_of_rows h11 h113 hpre h37 h38 h39 h312 (l4Rows_of_sporadic hsp)

end CFSG.Quasithin.A38c8
