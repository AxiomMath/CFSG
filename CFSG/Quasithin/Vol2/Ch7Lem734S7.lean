module

public import CFSG.Quasithin.Vol2.Ch7Lem734SL3
public import CFSG.Quasithin.Background.HA7NPrime

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Quasithin.E3 CFSG.Quasithin.H
open scoped IsMulCommutative

theorem stmt7_3_4_nPrime_S7Pair : Stmt7_3_4_nPrime_S7Pair := by
  intro G _ _ T L I _ hV hN hNM _ hrow
  obtain ⟨htw, hnat⟩ := hrow
  obtain ⟨φ, hφM, hinf, hsup, hniso⟩ := exists_twist_mem hV hN htw
  have hL : A7Four (V := IntMod (fsuV T I) hV) (autI hV (fsuL0 T L)) (intSub hV I) ⊥ := hnat
  exact A7.H8_A7Pair_nPrime hL (autI_top_le_normalizer hV hNM hφM) hinf hsup hniso
    (autI_fsuL0_le hV) (autI_top_le_normalizer hV hNM) hφM

end CFSG.Quasithin.H13
