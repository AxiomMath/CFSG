module

public import CFSG.Quasithin.Vol2.Ch7Lem734SL3
public import CFSG.Quasithin.Background.HSp4PairTorus

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Quasithin.E3 CFSG.Quasithin.H
open scoped IsMulCommutative

theorem stmt7_3_4_nPrime_Sp4Pair : Stmt7_3_4_nPrime_Sp4Pair := by
  intro G _ _ T L I _ hV hN hNM _ htw n hn hnat
  obtain ⟨φ, hφM, hinf, hsup, hniso⟩ := exists_twist_mem hV hN htw
  have hL : BinaryNaturalSp4 (V := IntMod (fsuV T I) hV) (autI hV (fsuL0 T L)) (intSub hV I) ⊥
      n := hnat
  exact Sp4.H7_Sp4Pair_nPrime hn hL (autI_top_le_normalizer hV hNM hφM) hinf hsup hniso
    (autI_fsuL0_le hV) (autI_top_le_normalizer hV hNM)

end CFSG.Quasithin.H13
