module

public import CFSG.Quasithin.Vol2.GoldschmidtF134OddLieU3OChar
public import CFSG.Quasithin.Vol2.GoldschmidtF134OddLieU3OCyc
public import CFSG.Quasithin.Vol2.GoldschmidtF134OddLieU3OInst
public import CFSG.Quasithin.Vol2.GoldschmidtF134OddLieU3OLinesCfg

public section

namespace CFSG.Quasithin.H13.NQCore

open CFSG.Assembly.LowTwoRank

theorem psu3Odd_simple : ∀ r : ℕ, r.Prime → r ≠ 2 →
    NoOddCfg fun (X : Type) [Group X] => StatedClassicalModel X .PSU 3 r 1 := by
  intro r hr hr2 A _ _ p hp L P T hp5 hL hcfg
  obtain ⟨a, ha, S, H, Q, hS2, hSi, -, hQH, hH, hQ, hQe⟩ := hcfg.exists_data hp5
  by_cases hpr : p = r
  · have hL' : StatedClassicalModel (↥L) .PSU 3 p 1 := hpr ▸ hL
    exact U3O.false_of_char hp5 (by omega) hL' hS2 hSi hQH hH hQ
  by_cases h1 : p ∣ r + 1
  · exact U3O.false_of_torusProp hcfg (U3O.pTorusProp_of_model hp.out hp5 h1 hL)
  · exact U3O.false_of_not_dvd hp5 hpr h1 hL (by omega) hQ hQe

end CFSG.Quasithin.H13.NQCore
