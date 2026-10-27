module

public import CFSG.Quasithin.Background.B15P4Layer2Main
public import CFSG.Quasithin.Background.B15P4Layer2A2

public section

namespace CFSG.Quasithin.B15P4

theorem asB15Part4 : AsB15Part4 :=
  part4_of_key fun _ _ _ hV _ _ hA hK hex hcomm hmin _ =>
    false_of_A2_ne_bot hV hA hK hex hcomm hmin (A2sub_ne_bot hV hA)

end CFSG.Quasithin.B15P4
