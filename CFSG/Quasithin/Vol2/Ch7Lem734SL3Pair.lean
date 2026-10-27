module

public import CFSG.Quasithin.Vol2.Ch7Lem734SL3
public import CFSG.Quasithin.Background.HSL3PairTorus

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Quasithin.E3 CFSG.Quasithin.H
open scoped IsMulCommutative

theorem stmt7_3_4_nPrime_SL3Pair : Stmt7_3_4_nPrime_SL3Pair := by
  intro G _ _ T L I _ hV hN hNM _ n hn hrow
  obtain ⟨htw, hnat⟩ := hrow
  obtain ⟨φ, hφM, hinf, hsup, hniso⟩ := exists_twist_mem hV hN htw
  have hL : BinaryNaturalSL (V := IntMod (fsuV T I) hV) (autI hV (fsuL0 T L)) (intSub hV I) ⊥
      3 n := hnat
  exact SL3Pair.H4_SL3Pair_nPrime hn hL (autI_top_le_normalizer hV hNM hφM) hinf hsup hniso
    (autI_fsuL0_le hV) (autI_top_le_normalizer hV hNM)

end CFSG.Quasithin.H13
