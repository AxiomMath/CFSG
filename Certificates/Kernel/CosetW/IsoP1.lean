module

public import CFSG.Quasithin.Recognition.L34AmalgamIsoCertInputs
public import Certificates.Data.Kernel.CosetW.IsoP1Snaps
public import CFSG.Certificates.Kernel.CosetW.Segments

public section

set_option maxRecDepth 400000

open CFSG.Quasithin.L34Amalgam CFSG.CosetTable CFSG.Certificates.CosetEnumeration
open CFSG.CosetTable.IsoP1Data

namespace CertificateChecks.CosetW

@[expose] def isoP1Params : Params := mkParamsW (2 * 5) (invArrW 5) (codes relsP1)
    (codes ((subsetOf 5 []).map fun x => [(x, true)]))

set_option maxHeartbeats 0 in
theorem isoP1_seg88 : felschW isoP1Params (64 * (100000 + 1) * (isoP1Params.L + 1)) 87 1
    (StW.init isoP1Params.L 100000) = isoP1S88 :=
  StW.eq_of_eqB (by decide +kernel)

set_option maxHeartbeats 0 in
theorem isoP1_seg194 : felschW isoP1Params (64 * (100000 + 1) * (isoP1Params.L + 1)) 106 88
    isoP1S88 = isoP1S194 :=
  StW.eq_of_eqB (by decide +kernel)

set_option maxHeartbeats 0 in
theorem isoP1_seg297 : felschW isoP1Params (64 * (100000 + 1) * (isoP1Params.L + 1)) 103 194
    isoP1S194 = isoP1S297 :=
  StW.eq_of_eqB (by decide +kernel)

set_option maxHeartbeats 0 in
theorem isoP1_seg418 : felschW isoP1Params (64 * (100000 + 1) * (isoP1Params.L + 1)) 121 297
    isoP1S297 = isoP1S418 :=
  StW.eq_of_eqB (by decide +kernel)

set_option maxHeartbeats 0 in
theorem isoP1_seg517 : felschW isoP1Params (64 * (100000 + 1) * (isoP1Params.L + 1)) 99 418
    isoP1S418 = isoP1S517 :=
  StW.eq_of_eqB (by decide +kernel)

set_option maxHeartbeats 0 in
theorem isoP1_seg614 : felschW isoP1Params (64 * (100000 + 1) * (isoP1Params.L + 1)) 97 517
    isoP1S517 = isoP1S614 :=
  StW.eq_of_eqB (by decide +kernel)

set_option maxHeartbeats 0 in
theorem isoP1_seg735 : felschW isoP1Params (64 * (100000 + 1) * (isoP1Params.L + 1)) 121 614
    isoP1S614 = isoP1S735 :=
  StW.eq_of_eqB (by decide +kernel)

set_option maxHeartbeats 0 in
theorem isoP1_seg838 : felschW isoP1Params (64 * (100000 + 1) * (isoP1Params.L + 1)) 103 735
    isoP1S735 = isoP1S838 :=
  StW.eq_of_eqB (by decide +kernel)

set_option maxHeartbeats 0 in
theorem isoP1_seg881 : felschW isoP1Params (64 * (100000 + 1) * (isoP1Params.L + 1)) 43 838
    isoP1S838 = isoP1S881 :=
  StW.eq_of_eqB (by decide +kernel)

set_option maxHeartbeats 0 in
theorem isoP1_seg967 : felschW isoP1Params (64 * (100000 + 1) * (isoP1Params.L + 1)) 86 881
    isoP1S881 = isoP1S967 :=
  StW.eq_of_eqB (by decide +kernel)

set_option maxHeartbeats 0 in
theorem isoP1_seg1231 : felschW isoP1Params (64 * (100000 + 1) * (isoP1Params.L + 1)) 264 967
    isoP1S967 = isoP1S1231 :=
  StW.eq_of_eqB (by decide +kernel)

set_option maxHeartbeats 0 in
theorem isoP1_seg1503 : felschW isoP1Params (64 * (100000 + 1) * (isoP1Params.L + 1)) 272 1231
    isoP1S1231 = isoP1S1503 :=
  StW.eq_of_eqB (by decide +kernel)

set_option maxHeartbeats 0 in
theorem isoP1_seg1880 : felschW isoP1Params (64 * (100000 + 1) * (isoP1Params.L + 1)) 377 1503
    isoP1S1503 = isoP1S1880 :=
  StW.eq_of_eqB (by decide +kernel)

set_option maxHeartbeats 0 in
theorem isoP1_seg2654 : felschW isoP1Params (64 * (100000 + 1) * (isoP1Params.L + 1)) 774 1880
    isoP1S1880 = isoP1S2654 :=
  StW.eq_of_eqB (by decide +kernel)

set_option maxHeartbeats 0 in
theorem isoP1_last :
    checkFromW isoP1Params (64 * (100000 + 1) * (isoP1Params.L + 1)) 97348 2654 isoP1S2654 960 = true := by
  decide +kernel

theorem isoP1_checkW : checkW (mkParamsW (2 * 5) (invArrW 5) (codes relsP1)
    (codes ((subsetOf 5 []).map fun x => [(x, true)]))) 100000 960 = true :=
  checkW_of_felschW (P := isoP1Params) rfl
    ((felschW_seg (b := 99914) isoP1_seg88).trans
      ((felschW_seg (b := 99808) isoP1_seg194).trans
      ((felschW_seg (b := 99705) isoP1_seg297).trans
      ((felschW_seg (b := 99584) isoP1_seg418).trans
      ((felschW_seg (b := 99485) isoP1_seg517).trans
      ((felschW_seg (b := 99388) isoP1_seg614).trans
      ((felschW_seg (b := 99267) isoP1_seg735).trans
      ((felschW_seg (b := 99164) isoP1_seg838).trans
      ((felschW_seg (b := 99121) isoP1_seg881).trans
      ((felschW_seg (b := 99035) isoP1_seg967).trans
      ((felschW_seg (b := 98771) isoP1_seg1231).trans
      ((felschW_seg (b := 98499) isoP1_seg1503).trans
      ((felschW_seg (b := 98122) isoP1_seg1880).trans
      (felschW_seg (b := 97348) isoP1_seg2654))))))))))))))
    isoP1_last

end CertificateChecks.CosetW
