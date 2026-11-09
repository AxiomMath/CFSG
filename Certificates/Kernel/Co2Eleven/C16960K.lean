module

public import Certificates.Kernel.Co2Eleven.Data7
public import Certificates.Kernel.SporSch.Co2M.Seeds
public import Certificates.Data.Kernel.Co2Eleven
public import CFSG.Certificates.Kernel.Spor.SlpMatSound
public import Certificates.Data.Kernel.RangeSplit
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelCo2Eleven

open CFSG.KC.Co2Eleven CertificateChecks.KernelSporSch.Co2M CFSG.KC.RangeSplit

@[expose] noncomputable def wcK7 : List (List Nat) := chunkK WN7 WF7

@[expose] noncomputable def wsK7 : List (List Int) := wcK7.map CFSG.KC.SlpM.decW

@[expose] def idW7 : List Nat := [4, 313, 314, 315, 316, 317, 318, 319]

@[expose] def chainW7 : List Nat :=
  [0, 1, 50, 56, 62, 108, 114, 120, 166, 172, 178, 184, 190, 196, 242, 248, 254, 300, 306, 312]

theorem letters7_h : (perm12 (AP 0) (CFSG.KS.pinvS (nat_lit 2300) (nat_lit 12) (CFSG.KS.mask (nat_lit 12)) (AP 0)) && perm12 (AP 1) (CFSG.KS.pinvS (nat_lit 2300) (nat_lit 12) (CFSG.KS.mask (nat_lit 12)) (AP 1))) = true := by
  quickRfl

theorem letters7_c0 : ((List.range wsK7.length).take 80).all
    (fun j => perm12 (WV7 j) (WVI7 j) && Nat.beq (WV7 j) (CFSG.KC.Co2Eleven.wordK (AP 0) (CFSG.KS.pinvS (nat_lit 2300) (nat_lit 12) (CFSG.KS.mask (nat_lit 12)) (AP 0)) (AP 1) (CFSG.KS.pinvS (nat_lit 2300) (nat_lit 12) (CFSG.KS.mask (nat_lit 12)) (AP 1))
      WV7 WVI7 (wsK7.getD j []))) = true := by
  quickRfl

theorem letters7_c1 : (((List.range wsK7.length).drop 80).take 80).all
    (fun j => perm12 (WV7 j) (WVI7 j) && Nat.beq (WV7 j) (CFSG.KC.Co2Eleven.wordK (AP 0) (CFSG.KS.pinvS (nat_lit 2300) (nat_lit 12) (CFSG.KS.mask (nat_lit 12)) (AP 0)) (AP 1) (CFSG.KS.pinvS (nat_lit 2300) (nat_lit 12) (CFSG.KS.mask (nat_lit 12)) (AP 1))
      WV7 WVI7 (wsK7.getD j []))) = true := by
  quickRfl

theorem letters7_c2 : ((((List.range wsK7.length).drop 80).drop 80).take 80).all
    (fun j => perm12 (WV7 j) (WVI7 j) && Nat.beq (WV7 j) (CFSG.KC.Co2Eleven.wordK (AP 0) (CFSG.KS.pinvS (nat_lit 2300) (nat_lit 12) (CFSG.KS.mask (nat_lit 12)) (AP 0)) (AP 1) (CFSG.KS.pinvS (nat_lit 2300) (nat_lit 12) (CFSG.KS.mask (nat_lit 12)) (AP 1))
      WV7 WVI7 (wsK7.getD j []))) = true := by
  quickRfl

theorem letters7_c3 : ((((List.range wsK7.length).drop 80).drop 80).drop 80).all
    (fun j => perm12 (WV7 j) (WVI7 j) && Nat.beq (WV7 j) (CFSG.KC.Co2Eleven.wordK (AP 0) (CFSG.KS.pinvS (nat_lit 2300) (nat_lit 12) (CFSG.KS.mask (nat_lit 12)) (AP 0)) (AP 1) (CFSG.KS.pinvS (nat_lit 2300) (nat_lit 12) (CFSG.KS.mask (nat_lit 12)) (AP 1))
      WV7 WVI7 (wsK7.getD j []))) = true := by
  quickRfl

theorem letters7_k : lettersK (AP 0) (AP 1) WV7 WVI7 wsK7 = true := by
  unfold lettersK
  exact andT letters7_h (all_cut (List.range wsK7.length) 80 letters7_c0 (all_cut ((List.range wsK7.length).drop 80) 80 letters7_c1 (all_cut (((List.range wsK7.length).drop 80).drop 80) 80 letters7_c2 (letters7_c3))))

theorem levels7_k : levelsK WV7 WVI7 R7 chainW7 3 4 7 SZ7 = true := by decide +kernel

theorem count7_k : countK WV7 WVI7 R7 chainW7 3 4 7 56 SZ7 = true := by decide +kernel

theorem misc7_k : miscK WV7 wsK7 chainW7 3 4 7 7 SZ7 = true := by decide +kernel

theorem cent7_k : centK WV7 wsK7 idW7 3 4 7 = true := by decide +kernel

end CertificateChecks.KernelCo2Eleven

end
