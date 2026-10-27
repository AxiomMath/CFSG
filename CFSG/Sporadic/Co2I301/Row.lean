module

public import CFSG.Sporadic.Co2I301.RowLayer
public import CFSG.Sporadic.Co2I301.RowMax
public import CFSG.LocalAnalysis.GLTheoremA.CatB.H301Transport

public noncomputable section

namespace CFSG.Sporadic.Co2I301

open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Sporadic.Co2Cert CFSG.Sporadic.Co2Schreier
  CFSG.HardMathSupport.Dickson.I271 CFSG.Open CFSG.Yardstones.Md0ec50421ce4
  CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.S8 CFSG.LocalAnalysis.GLTheoremA.H301


theorem i301ARowCfg_co2 (x : ↥co2P) (hx : (x : Equiv.Perm (Fin 2300)) = dP) :
    I301ARowCfg .co2 (locQ.subgroupOf co2P) (B1.subgroupOf co2P) x where
  hR := row_hR
  hB := row_hB
  hBN := row_hBN
  hd := row_hd x hx
  hI := row_hI x hx
  hK := row_hK x hx
  hR0 := row_hR0 x hx
  hR0t := Or.inr (by rw [row_hR0 x hx]; rfl)
  hK6 := Or.inr (row_hK6 x hx)
  hNL := fun h => absurd h (by decide)
  hMax := by
    rw [row_K x hx]
    exact row_hMax

theorem i301ARow_co2 :
    I301ARow .co2 := by
  obtain ⟨b⟩ := CFSG.Sporadic.Bridge.Co2.nonempty_mulEquiv
  have hd : dP ∈ co2P := locC_le_P gens_mem_locC.1
  exact i301ARow_of_model ↥co2P ⟨co2PermEquiv.symm.trans b⟩ (i301ARowCfg_co2 ⟨dP, hd⟩ rfl)

end CFSG.Sporadic.Co2I301
