module

public import CFSG.Certificates.Kernel.BabyMonster.BenesAlign
public import CFSG.Certificates.Kernel.BabyMonster.Dyadic.Gens
public import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CertificateChecks.KernelBM.Align

open CFSG.KC.BM CFSG.KC.BM.Dyadic

@[expose] noncomputable def monoMs : List (List Nat) :=
  [M0.b0, M1.b0, M2.b0, M3.b0, M4.b0, M5.b0, M6.b0, M7.b0, M8.b0, M9.b0, M10.b0, M11.b0, M12.b0,
    M13.b0, M14.b0, M15.b0, M16.b0, M17.b0, M18.b0, M19.b0, M20.b0, M21.b0, M22.b0, M23.b0,
    M26.b0]

@[expose] noncomputable def colors24 : List (List Nat) :=
  [CL24_0.b0, CL24_1.b0, CL24_2.b0, CL24_3.b0, CL24_4.b0, CL24_5.b0, CL24_6.b0, CL24_7.b0,
    CL24_8.b0, CL24_9.b0, CL24_10.b0, CL24_11.b0, CL24_12.b0, CL24_13.b0, CL24_14.b0, CL24_15.b0]

@[expose] noncomputable def colors25 : List (List Nat) :=
  [CL25_0.b0, CL25_1.b0, CL25_2.b0, CL25_3.b0, CL25_4.b0, CL25_5.b0, CL25_6.b0, CL25_7.b0,
    CL25_8.b0, CL25_9.b0, CL25_10.b0, CL25_11.b0, CL25_12.b0, CL25_13.b0, CL25_14.b0, CL25_15.b0]

theorem shifts : shifts16 dyDs = true := by quickRfl

theorem mono_aligned : allAlignedL monoMs = true := by quickRfl

theorem colors24_aligned : allAlignedL colors24 = true := by quickRfl

theorem colors25_aligned : allAlignedL colors25 = true := by quickRfl

theorem colors24_disj : selDisj colors24 = true := by quickRfl

theorem colors25_disj : selDisj colors25 = true := by quickRfl

end CertificateChecks.KernelBM.Align

end
