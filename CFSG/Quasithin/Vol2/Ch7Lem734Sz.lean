module

public import CFSG.Quasithin.Vol2.Ch7Lem734Rows
public import CFSG.Quasithin.Background.HSzNPrime
public import CFSG.Quasithin.Vol2.Ch7Setup

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Quasithin.E3 CFSG.Quasithin.H
open scoped IsMulCommutative

theorem stmt7_3_4_nPrime_Sz : Stmt7_3_4_nPrime_Sz := by
  intro G _ _ T L I _ hV _ hNM _ n hrow
  have hL : BinaryNaturalSz (V := IntMod (fsuV T I) hV) (autI hV (fsuL0 T L)) ⊤ ⊥ n := hrow
  exact H3_Sz_nPrime hL (autI_fsuL0_le hV) (autI_top_le_normalizer hV hNM)

theorem stmt7_2_1_m_Sz : Stmt7_2_1_m_Sz := by
  intro G _ _ T L I _ hV _ hNM _ n hrow
  have hL : BinaryNaturalSz (V := IntMod (fsuV T I) hV) (autI hV (fsuL0 T L)) ⊤ ⊥ n := hrow
  exact H3_Sz_mParam hL (autI_fsuL0_le hV) (autI_top_le_normalizer hV hNM)

end CFSG.Quasithin.H13
