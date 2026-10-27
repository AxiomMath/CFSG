module

public import CFSG.Quasithin.Vol2.Ch11SecO8A
public import CFSG.Quasithin.Vol2.Ch11SecCB51Facts

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecC

open CFSG.Open CFSG.Quasithin CFSG.Assembly.LowTwoRank

theorem factB42SL3_holds : FactB42SL3 := by
  intro F _ _ n hn hF V _ _ _ H U Z ⟨e⟩ hB
  have hH : Nat.card ↥H = 2 ^ (3 * n) * ((2 ^ (3 * n) - 1) * (2 ^ (2 * n) - 1)) := by
    rw [Nat.card_congr e.toEquiv, B51.card_SL3_eq_pow hF]
  rcases O8.b42_cases (by omega) (by omega) (by omega) hH hB with
    ⟨m, h1, -, hm⟩ | ⟨m, h1, h2, -⟩ | ⟨m, h1, h2, -⟩
  · obtain rfl : m = n := by omega
    exact hm
  · omega
  · omega

theorem factB42Sp4_holds : FactB42Sp4 := by
  intro F _ _ n hn hF V _ _ _ H U Z ⟨e⟩ hB
  have hH : Nat.card ↥H = 2 ^ (4 * n) * ((2 ^ (4 * n) - 1) * (2 ^ (2 * n) - 1)) := by
    rw [Nat.card_congr e.toEquiv, B51.card_Sp4_eq_pow hF, mul_comm (2 ^ (2 * n) - 1)]
  rcases O8.b42_cases (by omega) (by omega) (by omega) hH hB with
    ⟨m, h1, h2, -⟩ | ⟨m, h1, -, hm⟩ | ⟨m, h1, h2, -⟩
  · omega
  · obtain rfl : m = n := by omega
    exact hm
  · omega

theorem factB42G2_holds : FactB42G2 := by
  intro F _ _ n hn hF V _ _ _ H U Z ⟨e⟩ hB
  have hH : Nat.card ↥H = 2 ^ (6 * n) * ((2 ^ (6 * n) - 1) * (2 ^ (2 * n) - 1)) := by
    rw [Nat.card_congr e.toEquiv, B51.card_G2_eq_pow KGNat.factG2DerivedOrder_holds hn hF]
  rcases O8.b42_cases (by omega) (by omega) (by omega) hH hB with
    ⟨m, h1, h2, -⟩ | ⟨m, h1, h2, -⟩ | ⟨m, h1, -, hm⟩
  · omega
  · omega
  · obtain rfl : m = n := by omega
    exact hm

end CFSG.Quasithin.Vol2.Ch11.SecC
