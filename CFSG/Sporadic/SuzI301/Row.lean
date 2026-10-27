module

public import CFSG.Sporadic.SuzI301.RowLayer
public import CFSG.Sporadic.SuzI301.RowMax
public import CFSG.LocalAnalysis.GLTheoremA.CatB.H301Transport

public noncomputable section

namespace CFSG.Sporadic.SuzI301

open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Sporadic.SuzOddCore
  CFSG.ComponentClassification.AS81.SuzB0 CFSG.HardMathSupport.Dickson.I271 CFSG.Open
  CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.S8
  CFSG.LocalAnalysis.GLTheoremA.H301


theorem i301ARowCfg_suz (x : ↥suzM) (hx : (x : Equiv.Perm (Fin 1782)) = dP) :
    I301ARowCfg .suz (Q1.subgroupOf suzM) (B1.subgroupOf suzM) x where
  hR := row_hR
  hB := row_hB
  hBN := row_hBN
  hd := row_hd x hx
  hI := row_hI x hx
  hK := row_hK x hx
  hR0 := row_hR0 x hx
  hR0t := Or.inl (row_hR0t x hx)
  hK6 := Or.inr (row_hK6 x hx)
  hNL := fun h => absurd h (by decide)
  hMax := by
    rw [row_K x hx, bot_sup_eq]
    exact row_hMax

theorem i301ARow_suz :
    I301ARow .suz := by
  obtain ⟨b⟩ := CFSG.Sporadic.Bridge.Suz.nonempty_mulEquiv
  have hd : dP ∈ suzM := (invE_le_centM (by norm_num) gens_mem.1).2
  exact i301ARow_of_model ↥suzM ⟨suzEquivM.symm.trans b⟩ (i301ARowCfg_suz ⟨dP, hd⟩ rfl)

end CFSG.Sporadic.SuzI301
