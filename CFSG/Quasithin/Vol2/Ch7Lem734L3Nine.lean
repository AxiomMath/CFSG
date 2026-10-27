module

public import CFSG.Quasithin.Vol2.Ch7Lem734Rows
public import CFSG.Quasithin.Background.HL3NineNPrime
public import CFSG.Quasithin.Background.HL3NineM
public import CFSG.Quasithin.Vol2.Ch7Setup

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Quasithin.E3 CFSG.Quasithin.H
open scoped IsMulCommutative

theorem stmt7_3_4_nPrime_L3Nine : Stmt7_3_4_nPrime_L3Nine := by
  intro G _ _ T L I _ hV _ hNM _ n hrow
  obtain ⟨hn, hnat⟩ := hrow
  have hL : BinaryNineTensor (V := IntMod (fsuV T I) hV) (autI hV (fsuL0 T L)) ⊤ ⊥ n := hnat
  exact H42_L3Nine_nPrime hn hL (autI_fsuL0_le hV) (autI_top_le_normalizer hV hNM)

theorem stmt7_2_1_m_L3Nine : Stmt7_2_1_m_L3Nine := by
  intro G _ _ T L I _ hV _ hNM _ n hrow
  obtain ⟨hn, hnat⟩ := hrow
  have hL : BinaryNineTensor (V := IntMod (fsuV T I) hV) (autI hV (fsuL0 T L)) ⊤ ⊥ n := hnat
  exact H42_L3Nine_mParam hn hL (autI_fsuL0_le hV) (autI_top_le_normalizer hV hNM)

end CFSG.Quasithin.H13
