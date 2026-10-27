module

public import CFSG.Quasithin.H13.A6S1372L76U
public import CFSG.Quasithin.H13.A6S1372L76P3

public section

namespace CFSG.Quasithin.H13.A6

open Equiv CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits
open CFSG.QuasithinUnique.Bridge
open scoped Pointwise IsMulCommutative

theorem lem1376Full_of (hB : Lem1376L1K) (h3 : Lem1376NThree)
    (h5 : Lem1376Five) (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h13314 : Stmt13_3_14)
    (h13315 : Stmt13_3_15) (h1356two : Input1356Two) (h1337 : Stmt13_3_7) : Lem1376Full := by
  intro G _ _ T L V S hNS hNU H hH hab _ K hK
  refine ⟨fun n hn hBN => S.lem1376_one hB h3 h37 h38 h13314 h13315 h1356two h1337 hNS hNU hH hab
      hK n hn hBN,
    S.lem1376_two hB h37 h38 h13314 h13315 h1356two hNS hNU hH hab hK,
    fun n hAN => S.lem1376_three hB h37 h38 h13314 h13315 h1356two h1337 hNS hNU hH hab hK n hAN,
    S.lem1376_extSq4 hB h37 h38 h13314 h13315 h1356two hNS hNU hH hab hK,
    S.lem1376_four hB h37 h38 h13315 h1356two h1337 hNS hNU hH hab hK,
    fun n hSL => ?_, fun n hSp => ?_, fun n hG2 => ?_⟩
  · exact (h5 G T L V S hNS hNU H hH hab K hK (hB G T L V S hNS hNU H hH hab K hK
      (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨n, hSL⟩)))))))).1 n hSL
  · exact (h5 G T L V S hNS hNU H hH hab K hK (hB G T L V S hNS hNU H hH hab K hK
      (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨n, hSp⟩))))))))).2.1 n hSp
  · exact (h5 G T L V S hNS hNU H hH hab K hK (hB G T L V S hNS hNU H hH hab K hK
      (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨n, hG2⟩))))))))).2.2 n hG2

end CFSG.Quasithin.H13.A6
