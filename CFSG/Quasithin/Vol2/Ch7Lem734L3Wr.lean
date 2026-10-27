module

public import CFSG.Quasithin.Vol2.Ch7Lem734Rows
public import CFSG.Quasithin.Background.HL3WrMParam
public import CFSG.Quasithin.Background.HL3WrNPrime
public import CFSG.Quasithin.Vol2.Ch7Setup

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Quasithin.E3 CFSG.Quasithin.H
open scoped IsMulCommutative

theorem stmt7_3_4_nPrime_L3Wreath : Stmt7_3_4_nPrime_L3Wreath := by
  intro G _ _ T L I _ hV _ hNM _ hrow
  obtain ⟨-, hreal⟩ := hrow
  have hL : (tensorPairModel L3Wr.SL32 L3Wr.SL32).RealizesMod (V := IntMod (fsuV T I) hV)
      (autI hV (fsuL0 T L)) := hreal
  exact L3Wr.H44_L3Wreath_nPrime hL (autI_fsuL0_le hV) (autI_top_le_normalizer hV hNM)

theorem stmt7_2_1_m_L3Wreath : Stmt7_2_1_m_L3Wreath := by
  intro G _ _ T L I _ hV _ hNM _ hrow
  obtain ⟨-, hreal⟩ := hrow
  have hL : (tensorPairModel L3Wr.SL32 L3Wr.SL32).RealizesMod (V := IntMod (fsuV T I) hV)
      (autI hV (fsuL0 T L)) := hreal
  exact L3Wr.H44_L3Wreath_mParam hL (autI_top_le_normalizer hV hNM)

end CFSG.Quasithin.H13
