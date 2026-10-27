module

public import Certificates.Kernel.AE5Sq.Data

public noncomputable section

namespace CFSG.KD.AE5Sq

open CFSG.KC.WrTwin CFSG.KC.WrPack CFSG.ClassicalInvolution.Q3.AE CFSG.ClassicalInvolution.Q3.AE.Wr
  Certificates.AE117 Certificates.AE5Sq

theorem ae5s_chain : chainOK (fun _ => true) [0, 1, 2, 3] chain5 = true := by decide +kernel

theorem ae5s_chain_len : (chain5.map List.length).prod = 120 := by decide +kernel

theorem ae5s_pins : (Ylit == Y60W.map enc && Vlit == Vall 5 && Nat.beq a0lit (enc (a0 ())) &&
    Nat.beq b0lit (enc (b0 ())) && Nat.beq pilit (enc (allOnes 5))) = true := by
  decide +kernel

theorem ae5s_sq : sqOK 5 pilit [a0lit, b0lit] P120 Vlit Ylit = true := by decide +kernel

theorem ae5s_pins2 : (P60lit == P60W.map lvl && V16lit == Veven 5 &&
    M10lit == M10W.map (·.map enc) && Nat.beq e10 654820258320) = true := by
  decide +kernel

theorem ae5s_q8 : q8OK 5 654820258320 pilit P60lit V16lit M10lit = true := by decide +kernel

theorem ae5s_gen : (alphaQ.all fun a => [true, false].all fun b =>
    genB (memLC a.1 a.2.1 a.2.2.1 a.2.2.2 b)) = true := by
  decide +kernel

theorem ae5s_ord4 : Y60W.all ord4Pi = true := by decide +kernel

end CFSG.KD.AE5Sq

end
