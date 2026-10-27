module

public import CFSG.Quasithin.Vol2.Ch12Sec2Lem25J

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique

namespace Lem25

theorem prime_eq_three
    (h331 : Stmt3_3_1) (h1222 : Stmt12_2_2) (h323 : Stmt3_2_3)
    (h1216 : Stmt12_2_16) (h1220 : Stmt12_2_20) (hY : Lem12225YNormal) {G : Type} [Group G]
    [Finite G] {T L V H P U I : Subgroup G} {h : G} {n p : ℕ} (hH : Hyp1223 G T L V)
    (hNE : NoEscape12_2_13 L V) (hC : Config12_2_24 T L V H P U I h n p) : p = 3 := by
  by_cases hn3 : n = 3
  · exact prime_eq_three_of_three h331 h1222 h323 h1216 h1220 hH hNE hC hn3
  · exact prime_eq_three_of_yNormal h331 h1222 h323 h1216 h1220 hY hH hNE hC hn3

end Lem25

open Lem25

theorem lem12226Split_of
    (h331 : Stmt3_3_1) (h1222 : Stmt12_2_2) (h323 : Stmt3_2_3)
    (h1216 : Stmt12_2_16) (h1220 : Stmt12_2_20) (hY : Lem12225YNormal) : Lem12226Split := by
  intro G _ _ T L V H P U I h n p hH hNE hC
  exact exists_complement_of_three h1222 hH hC
    (prime_eq_three h331 h1222 h323 h1216 h1220 hY hH hNE hC)

end CFSG.Quasithin.H13
