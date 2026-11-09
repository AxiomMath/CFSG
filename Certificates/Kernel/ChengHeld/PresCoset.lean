module

public import CFSG.Certificates.Kernel.CosetW.Columns
public import Certificates.Data.ChengHeldPres
public import Certificates.Data.Kernel.CosetW.SegChain
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Common.NatVal

public section

set_option maxRecDepth 400000

open CFSG.CosetTable CFSG.OddStandard.ChengHeldData

namespace CertificateChecks.KernelChengHeld

abbrev P40 : Params :=
  mkParamsW (cols (relWords4 0)).length (colInv (relWords4 0))
    (colCodes (relWords4 0) (relWords4 0))
    (colCodes (relWords4 0) ((subsetOf _ []).map fun x => [(x, true)]))

theorem e40_hs : P40.subs = [] := rfl

#kc_natval E40T1 := (felschW P40 (64 * (2000 + 1) * (P40.L + 1)) 64 1 (StW.init P40.L 2000)).tab.t
#kc_natval E40F1 := (felschW P40 (64 * (2000 + 1) * (P40.L + 1)) 64 1 (StW.init P40.L 2000)).fwd.t
#kc_natval E40Q1 := (felschW P40 (64 * (2000 + 1) * (P40.L + 1)) 64 1 (StW.init P40.L 2000)).par.t
#kc_natval E40N1 := (felschW P40 (64 * (2000 + 1) * (P40.L + 1)) 64 1 (StW.init P40.L 2000)).next

@[expose] noncomputable def e40S1 : StW :=
  ⟨⟨(2000 + 1) * P40.L, E40T1⟩, ⟨2000 + 1, E40F1⟩, ⟨2000 + 1, E40Q1⟩, E40N1, #[], #[], 0,
    false⟩

set_option maxHeartbeats 0 in
theorem e40_h1 : felschW P40 (64 * (2000 + 1) * (P40.L + 1)) 64 1 (StW.init P40.L 2000) = e40S1 :=
  StW.eq_of_eqB (by quickRfl)

#kc_natval E40T2 := (felschW P40 (64 * (2000 + 1) * (P40.L + 1)) 64 (1 + 64) e40S1).tab.t
#kc_natval E40F2 := (felschW P40 (64 * (2000 + 1) * (P40.L + 1)) 64 (1 + 64) e40S1).fwd.t
#kc_natval E40Q2 := (felschW P40 (64 * (2000 + 1) * (P40.L + 1)) 64 (1 + 64) e40S1).par.t
#kc_natval E40N2 := (felschW P40 (64 * (2000 + 1) * (P40.L + 1)) 64 (1 + 64) e40S1).next

@[expose] noncomputable def e40S2 : StW :=
  ⟨⟨(2000 + 1) * P40.L, E40T2⟩, ⟨2000 + 1, E40F2⟩, ⟨2000 + 1, E40Q2⟩, E40N2, #[], #[], 0,
    false⟩

set_option maxHeartbeats 0 in
theorem e40_h2 : felschW P40 (64 * (2000 + 1) * (P40.L + 1)) 64 (1 + 64) e40S1 = e40S2 :=
  StW.eq_of_eqB (by quickRfl)

#kc_natval E40T3 := (felschW P40 (64 * (2000 + 1) * (P40.L + 1)) 64 (1 + 64 + 64) e40S2).tab.t
#kc_natval E40F3 := (felschW P40 (64 * (2000 + 1) * (P40.L + 1)) 64 (1 + 64 + 64) e40S2).fwd.t
#kc_natval E40Q3 := (felschW P40 (64 * (2000 + 1) * (P40.L + 1)) 64 (1 + 64 + 64) e40S2).par.t
#kc_natval E40N3 := (felschW P40 (64 * (2000 + 1) * (P40.L + 1)) 64 (1 + 64 + 64) e40S2).next

@[expose] noncomputable def e40S3 : StW :=
  ⟨⟨(2000 + 1) * P40.L, E40T3⟩, ⟨2000 + 1, E40F3⟩, ⟨2000 + 1, E40Q3⟩, E40N3, #[], #[], 0,
    false⟩

set_option maxHeartbeats 0 in
theorem e40_h3 : felschW P40 (64 * (2000 + 1) * (P40.L + 1)) 64 (1 + 64 + 64) e40S2 = e40S3 :=
  StW.eq_of_eqB (by quickRfl)

set_option maxHeartbeats 0 in
theorem e40_hc : checkFromW P40 (64 * (2000 + 1) * (P40.L + 1)) 1809 (1 + 64 + 64 + 64) e40S3 256 = true := by quickRfl

set_option maxHeartbeats 0 in
theorem e40 : subsetCheckC (relWords4 0) [] 2000 256 = true := by
  rw [subsetCheckC_eq_checkW _ _ (by decide +kernel)]
  exact checkW_of_seg4 (P := P40) (a₁ := 64) (a₂ := 64) (a₃ := 64) (r := 1809)
    e40_hs rfl e40_h1 e40_h2 e40_h3 e40_hc

abbrev P41 : Params :=
  mkParamsW (cols (relWords4 1)).length (colInv (relWords4 1))
    (colCodes (relWords4 1) (relWords4 1))
    (colCodes (relWords4 1) ((subsetOf _ []).map fun x => [(x, true)]))

theorem e41_hs : P41.subs = [] := rfl

#kc_natval E41T1 := (felschW P41 (64 * (2000 + 1) * (P41.L + 1)) 64 1 (StW.init P41.L 2000)).tab.t
#kc_natval E41F1 := (felschW P41 (64 * (2000 + 1) * (P41.L + 1)) 64 1 (StW.init P41.L 2000)).fwd.t
#kc_natval E41Q1 := (felschW P41 (64 * (2000 + 1) * (P41.L + 1)) 64 1 (StW.init P41.L 2000)).par.t
#kc_natval E41N1 := (felschW P41 (64 * (2000 + 1) * (P41.L + 1)) 64 1 (StW.init P41.L 2000)).next

@[expose] noncomputable def e41S1 : StW :=
  ⟨⟨(2000 + 1) * P41.L, E41T1⟩, ⟨2000 + 1, E41F1⟩, ⟨2000 + 1, E41Q1⟩, E41N1, #[], #[], 0,
    false⟩

set_option maxHeartbeats 0 in
theorem e41_h1 : felschW P41 (64 * (2000 + 1) * (P41.L + 1)) 64 1 (StW.init P41.L 2000) = e41S1 :=
  StW.eq_of_eqB (by quickRfl)

#kc_natval E41T2 := (felschW P41 (64 * (2000 + 1) * (P41.L + 1)) 64 (1 + 64) e41S1).tab.t
#kc_natval E41F2 := (felschW P41 (64 * (2000 + 1) * (P41.L + 1)) 64 (1 + 64) e41S1).fwd.t
#kc_natval E41Q2 := (felschW P41 (64 * (2000 + 1) * (P41.L + 1)) 64 (1 + 64) e41S1).par.t
#kc_natval E41N2 := (felschW P41 (64 * (2000 + 1) * (P41.L + 1)) 64 (1 + 64) e41S1).next

@[expose] noncomputable def e41S2 : StW :=
  ⟨⟨(2000 + 1) * P41.L, E41T2⟩, ⟨2000 + 1, E41F2⟩, ⟨2000 + 1, E41Q2⟩, E41N2, #[], #[], 0,
    false⟩

set_option maxHeartbeats 0 in
theorem e41_h2 : felschW P41 (64 * (2000 + 1) * (P41.L + 1)) 64 (1 + 64) e41S1 = e41S2 :=
  StW.eq_of_eqB (by quickRfl)

#kc_natval E41T3 := (felschW P41 (64 * (2000 + 1) * (P41.L + 1)) 64 (1 + 64 + 64) e41S2).tab.t
#kc_natval E41F3 := (felschW P41 (64 * (2000 + 1) * (P41.L + 1)) 64 (1 + 64 + 64) e41S2).fwd.t
#kc_natval E41Q3 := (felschW P41 (64 * (2000 + 1) * (P41.L + 1)) 64 (1 + 64 + 64) e41S2).par.t
#kc_natval E41N3 := (felschW P41 (64 * (2000 + 1) * (P41.L + 1)) 64 (1 + 64 + 64) e41S2).next

@[expose] noncomputable def e41S3 : StW :=
  ⟨⟨(2000 + 1) * P41.L, E41T3⟩, ⟨2000 + 1, E41F3⟩, ⟨2000 + 1, E41Q3⟩, E41N3, #[], #[], 0,
    false⟩

set_option maxHeartbeats 0 in
theorem e41_h3 : felschW P41 (64 * (2000 + 1) * (P41.L + 1)) 64 (1 + 64 + 64) e41S2 = e41S3 :=
  StW.eq_of_eqB (by quickRfl)

set_option maxHeartbeats 0 in
theorem e41_hc : checkFromW P41 (64 * (2000 + 1) * (P41.L + 1)) 1809 (1 + 64 + 64 + 64) e41S3 256 = true := by quickRfl

set_option maxHeartbeats 0 in
theorem e41 : subsetCheckC (relWords4 1) [] 2000 256 = true := by
  rw [subsetCheckC_eq_checkW _ _ (by decide +kernel)]
  exact checkW_of_seg4 (P := P41) (a₁ := 64) (a₂ := 64) (a₃ := 64) (r := 1809)
    e41_hs rfl e41_h1 e41_h2 e41_h3 e41_hc

set_option maxHeartbeats 0 in
theorem e2 : subsetCheckC relWords2 [] 2000 128 = true := by
  rw [subsetCheckC_eq_checkW _ _ (by decide +kernel)]
  decide +kernel

theorem pres4_true : pres4OK = true := by
  unfold pres4OK
  rw [e40, e41]
  rfl

theorem pres2_true : pres2OK = true := e2

end CertificateChecks.KernelChengHeld

end
