module

public import CFSG.Sporadic.ThI301.RowMax
public import CFSG.LocalAnalysis.GLTheoremA.CatB.H301Transport

public noncomputable section

namespace CFSG.Sporadic.ThI301

open CFSG.Sporadic.Th CFSG.Sporadic.Th.Max3 CFSG.Sporadic.Th.Recog CFSG.Open
  CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.S8
  CFSG.LocalAnalysis.GLTheoremA.H301


theorem i301ARowCfg_th : I301ARowCfg .th Max3.Q B1 (hswJ 6) where
  hR := row_hR
  hB := row_hB
  hBN := row_hBN
  hd := row_hd
  hI := row_hI
  hK := row_hK
  hR0 := row_hR0
  hR0t := Or.inl row_hR0t
  hK6 := Or.inr row_hK6
  hNL := fun h => absurd h (by decide)
  hMax := row_hMax

theorem i301ARow_th : I301ARow .th := by
  obtain ⟨b⟩ := CFSG.Sporadic.Bridge.Th.nonempty_mulEquiv
  exact @i301ARow_of_model .th ↥J (Subgroup.toGroup J) _ ⟨thEquivJ.symm.trans b⟩ _ _ _
    i301ARowCfg_th

end CFSG.Sporadic.ThI301
