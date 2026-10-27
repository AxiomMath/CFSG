module

public import CFSG.Quasithin.Vol2.Ch7Lem734Rows
public import CFSG.Quasithin.Background.HSU3Torus
public import CFSG.Quasithin.Vol2.Ch7Setup

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Quasithin.E3 CFSG.Quasithin.H
open scoped IsMulCommutative

theorem stmt7_3_4_nPrime_SU3 : Stmt7_3_4_nPrime_SU3 := by
  intro G _ _ T L I _ hV _ hNM _ n hn hnat
  have hL : BinaryNaturalSU3 (V := IntMod (fsuV T I) hV) (autI hV (fsuL0 T L)) ⊤ ⊥ n := hnat
  exact H2_SU3_nPrime hn hL (autI_fsuL0_le hV) (autI_top_le_normalizer hV hNM)

end CFSG.Quasithin.H13
