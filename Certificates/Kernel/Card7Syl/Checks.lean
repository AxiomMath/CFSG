module

public import Certificates.Data.Kernel.PermCent.ForceCV
public import CFSG.GH74.GLS.C3.Prop121.Card7SylInputs

public section

namespace Certificates.Kernel.Card7Syl

open CFSG.Certificates.Kernel.PkCV CFSG.GH74.GLS.C3.Prop121.Card7.Syl CFSG.GH74.GLS.C3.Prop121.Card7.HC
  CFSG.GH74.GLS.C3.Layer2

theorem sl_length : decide (SL.length = 128) = true := by
  decide +kernel

theorem sl_one : decide ((1 : P11) ∈ SL) = true := by
  decide +kernel

theorem sl_count : decide (SL.countP (fun σ => decide (σ * σ = 1 ∧ σ ≠ 1 ∧ numMoved σ = 4)) = 14) =
    true := by
  decide +kernel

theorem sl_groupF : groupF (SL.map cOf) = true := by
  decide +kernel

end Certificates.Kernel.Card7Syl

end
