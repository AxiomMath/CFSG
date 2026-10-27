module

public import CFSG.Quasithin.H13.A6S13821L32HatFinal
public import CFSG.Quasithin.H13.A6S13821L32HatC5

public section

namespace CFSG.Quasithin.H13.A6

namespace L32Hat

theorem case13821L32Hat_holds
    (h16 : Lem13816) (h36c : QuasithinUnique.Vol2Native.A36CoreForSQTKCat) (h37 : A37ForSQTK)
    (h38 : A38ForSQTK) (h139 : Stmt13_3_9) (h1334 : Stmt13_3_4) (h13 : Lem13813)
    (h13314 : Stmt13_3_14) (h13315 : Stmt13_3_15) (h1356two : Input1356Two) :
    Case13821L32Hat :=
  case13821L32Hat_of_c h16 h36c h37 h38 h139 h1334 h13 h13314 h13315 h1356two
    (fun _ _ _ _ _ _ S hS hhat _ hH _ hK hP hKn hHK _ =>
      CFSG.Quasithin.H13.A6.L32HatC5.hC_holds h139 h37 h38 h1334 h13 hS hhat hH hK hKn hP hHK)

end L32Hat

end CFSG.Quasithin.H13.A6
