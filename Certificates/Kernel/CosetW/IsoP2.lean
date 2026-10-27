module

public import CFSG.Quasithin.Recognition.L34AmalgamIsoCertInputs
public import Certificates.Data.Kernel.CosetW.IsoP2Snaps
public import CFSG.Certificates.Kernel.CosetW.Segments

public section

set_option maxRecDepth 400000

open CFSG.Quasithin.L34Amalgam CFSG.CosetTable CFSG.Certificates.CosetEnumeration
open CFSG.CosetTable.IsoP2Data

namespace CertificateChecks.CosetW

@[expose] def isoP2Params : Params := mkParamsW (2 * 5) (invArrW 5) (codes relsP2)
    (codes ((subsetOf 5 []).map fun x => [(x, true)]))

set_option maxHeartbeats 0 in
theorem isoP2_seg95 : felschW isoP2Params (64 * (100000 + 1) * (isoP2Params.L + 1)) 94 1
    (StW.init isoP2Params.L 100000) = isoP2S95 :=
  StW.eq_of_eqB (by decide +kernel)

set_option maxHeartbeats 0 in
theorem isoP2_seg188 : felschW isoP2Params (64 * (100000 + 1) * (isoP2Params.L + 1)) 93 95
    isoP2S95 = isoP2S188 :=
  StW.eq_of_eqB (by decide +kernel)

set_option maxHeartbeats 0 in
theorem isoP2_seg280 : felschW isoP2Params (64 * (100000 + 1) * (isoP2Params.L + 1)) 92 188
    isoP2S188 = isoP2S280 :=
  StW.eq_of_eqB (by decide +kernel)

set_option maxHeartbeats 0 in
theorem isoP2_seg371 : felschW isoP2Params (64 * (100000 + 1) * (isoP2Params.L + 1)) 91 280
    isoP2S280 = isoP2S371 :=
  StW.eq_of_eqB (by decide +kernel)

set_option maxHeartbeats 0 in
theorem isoP2_seg461 : felschW isoP2Params (64 * (100000 + 1) * (isoP2Params.L + 1)) 90 371
    isoP2S371 = isoP2S461 :=
  StW.eq_of_eqB (by decide +kernel)

set_option maxHeartbeats 0 in
theorem isoP2_seg553 : felschW isoP2Params (64 * (100000 + 1) * (isoP2Params.L + 1)) 92 461
    isoP2S461 = isoP2S553 :=
  StW.eq_of_eqB (by decide +kernel)

set_option maxHeartbeats 0 in
theorem isoP2_seg645 : felschW isoP2Params (64 * (100000 + 1) * (isoP2Params.L + 1)) 92 553
    isoP2S553 = isoP2S645 :=
  StW.eq_of_eqB (by decide +kernel)

set_option maxHeartbeats 0 in
theorem isoP2_seg738 : felschW isoP2Params (64 * (100000 + 1) * (isoP2Params.L + 1)) 93 645
    isoP2S645 = isoP2S738 :=
  StW.eq_of_eqB (by decide +kernel)

set_option maxHeartbeats 0 in
theorem isoP2_seg851 : felschW isoP2Params (64 * (100000 + 1) * (isoP2Params.L + 1)) 113 738
    isoP2S738 = isoP2S851 :=
  StW.eq_of_eqB (by decide +kernel)

set_option maxHeartbeats 0 in
theorem isoP2_seg911 : felschW isoP2Params (64 * (100000 + 1) * (isoP2Params.L + 1)) 60 851
    isoP2S851 = isoP2S911 :=
  StW.eq_of_eqB (by decide +kernel)

set_option maxHeartbeats 0 in
theorem isoP2_seg1000 : felschW isoP2Params (64 * (100000 + 1) * (isoP2Params.L + 1)) 89 911
    isoP2S911 = isoP2S1000 :=
  StW.eq_of_eqB (by decide +kernel)

set_option maxHeartbeats 0 in
theorem isoP2_seg1010 : felschW isoP2Params (64 * (100000 + 1) * (isoP2Params.L + 1)) 10 1000
    isoP2S1000 = isoP2S1010 :=
  StW.eq_of_eqB (by decide +kernel)

set_option maxHeartbeats 0 in
theorem isoP2_seg1235 : felschW isoP2Params (64 * (100000 + 1) * (isoP2Params.L + 1)) 225 1010
    isoP2S1010 = isoP2S1235 :=
  StW.eq_of_eqB (by decide +kernel)

set_option maxHeartbeats 0 in
theorem isoP2_seg1591 : felschW isoP2Params (64 * (100000 + 1) * (isoP2Params.L + 1)) 356 1235
    isoP2S1235 = isoP2S1591 :=
  StW.eq_of_eqB (by decide +kernel)

set_option maxHeartbeats 0 in
theorem isoP2_seg2008 : felschW isoP2Params (64 * (100000 + 1) * (isoP2Params.L + 1)) 417 1591
    isoP2S1591 = isoP2S2008 :=
  StW.eq_of_eqB (by decide +kernel)

set_option maxHeartbeats 0 in
theorem isoP2_seg2561 : felschW isoP2Params (64 * (100000 + 1) * (isoP2Params.L + 1)) 553 2008
    isoP2S2008 = isoP2S2561 :=
  StW.eq_of_eqB (by decide +kernel)

set_option maxHeartbeats 0 in
theorem isoP2_seg3853 : felschW isoP2Params (64 * (100000 + 1) * (isoP2Params.L + 1)) 1292 2561
    isoP2S2561 = isoP2S3853 :=
  StW.eq_of_eqB (by decide +kernel)

set_option maxHeartbeats 0 in
theorem isoP2_seg4371 : felschW isoP2Params (64 * (100000 + 1) * (isoP2Params.L + 1)) 518 3853
    isoP2S3853 = isoP2S4371 :=
  StW.eq_of_eqB (by decide +kernel)

set_option maxHeartbeats 0 in
theorem isoP2_last :
    checkFromW isoP2Params (64 * (100000 + 1) * (isoP2Params.L + 1)) 95631 4371 isoP2S4371 960 = true := by
  decide +kernel

theorem isoP2_checkW : checkW (mkParamsW (2 * 5) (invArrW 5) (codes relsP2)
    (codes ((subsetOf 5 []).map fun x => [(x, true)]))) 100000 960 = true :=
  checkW_of_felschW (P := isoP2Params) rfl
    ((felschW_seg (b := 99907) isoP2_seg95).trans
      ((felschW_seg (b := 99814) isoP2_seg188).trans
      ((felschW_seg (b := 99722) isoP2_seg280).trans
      ((felschW_seg (b := 99631) isoP2_seg371).trans
      ((felschW_seg (b := 99541) isoP2_seg461).trans
      ((felschW_seg (b := 99449) isoP2_seg553).trans
      ((felschW_seg (b := 99357) isoP2_seg645).trans
      ((felschW_seg (b := 99264) isoP2_seg738).trans
      ((felschW_seg (b := 99151) isoP2_seg851).trans
      ((felschW_seg (b := 99091) isoP2_seg911).trans
      ((felschW_seg (b := 99002) isoP2_seg1000).trans
      ((felschW_seg (b := 98992) isoP2_seg1010).trans
      ((felschW_seg (b := 98767) isoP2_seg1235).trans
      ((felschW_seg (b := 98411) isoP2_seg1591).trans
      ((felschW_seg (b := 97994) isoP2_seg2008).trans
      ((felschW_seg (b := 97441) isoP2_seg2561).trans
      ((felschW_seg (b := 96149) isoP2_seg3853).trans
      (felschW_seg (b := 95631) isoP2_seg4371))))))))))))))))))
    isoP2_last

end CertificateChecks.CosetW
