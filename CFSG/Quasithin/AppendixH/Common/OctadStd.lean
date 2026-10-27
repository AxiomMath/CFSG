module

public import CFSG.Quasithin.AppendixH.Common.OctadTwoCore

public section

open scoped Pointwise

namespace CFSG.ASVolI.AppH

open CFSG.ASVolI.ChH CFSG.Monster.Code CFSG.Open

theorem mem_octad0_iff {i : Fin 24} : i ∈ octad0 ↔ (i : ℕ) < 8 := by
  simp [octad0]

theorem card_octStab_octad0 :
    Nat.card (octStab octad0) = 322560 :=
  card_octStab isOctad_octad0

theorem pCoreOf_octStab_octad0 :
    pCoreOf 2 (octStab octad0) = CFSG.Quasithin.H.Mathieu.H16Pf.fixO := by
  rw [pCoreOf_octStab isOctad_octad0, octFix_octad0]

end CFSG.ASVolI.AppH
