module

public import Certificates.Kernel.AE6Twin.Data

public noncomputable section

namespace CFSG.KD.AE6Twin

open CFSG.KC.WrTwin CFSG.KC.AE6TwinK CFSG.ClassicalInvolution.Q3.AE
  CFSG.ClassicalInvolution.Q3.AE.Wr Certificates.AE117

theorem ae6t_chain : chainOK (fun _ => true) [0, 1, 2, 3, 4] chain6 = true := by decide +kernel

theorem ae6t_chain_len : (chain6.map List.length).prod = 720 := by decide +kernel

theorem ae6t_cent : centOK pi12 (gens0.map enc) P720 V64 (Crec.map enc) = true := by
  decide +kernel

theorem ae6t_tv : tvOK e12 pi12 (enc z0) P720 E32 (Dl.map enc) = true := by decide +kernel

theorem ae6t_trans : transOK pi12 b01 (transW.map lvl) (U15.map enc) = true := by decide +kernel

theorem ae6t_ucover : E32.all (fun v => inModPi pi12 v (((1 : Wr 6) :: U15).map enc)) = true := by
  decide +kernel

theorem ae6t_small : (centUOK z0 Crec && dlOK z0 Crec Dl && twin3OK z0 Crec &&
    twin2OK (mem0 true) (mem0 false) && twin2OK (mem0 false) (mem0 true)) = true := by
  decide +kernel

end CFSG.KD.AE6Twin

end
