module

public import Certificates.Kernel.AE6CertE.ChainV0
public import Certificates.Kernel.AE6CertE.ChainV1
public import Certificates.Kernel.AE6CertE.ChainV2
public import Certificates.Kernel.AE6CertE.ChainUP
public import Certificates.Kernel.AE6CertE.ChainPP
public import Certificates.Kernel.AE6F.Final
public import Certificates.Data.AE6CertE

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelAE6CertE

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.SporSch.MOC Certificates.AE6CertE
  Certificates.AE6Model CertificateChecks.KernelAE6F Certificates.AE6CertEK CFSG.Sporadic.Th
  CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.Native CFSG.Monster.B.Mathieu
  CFSG.Monster.B.Co2.Native

theorem eGens_length (L : List ℕ) : (eGens L).length = L.length := by
  simp [eGens]

theorem eGens_getD {L : List ℕ} {j : ℕ} (hj : j < L.length) :
    (eGens L).getD j 1 = (curtisPerms ()).getD L[j] 1 := by
  rw [List.getD_eq_getElem _ _ (by rw [eGens_length]; exact hj)]
  simp [eGens]

theorem eGens_img {L : List ℕ} (hL : ∀ i ∈ L, i < 8) {S : ℕ → ℕ}
    (hS : ∀ j < L.length, S j = CertificateChecks.KernelO8.AP.S (L.getD j 0)) :
    ∀ j < (eGens L).length, imageList ((eGens L).getD j 1) = (unpack 360 9 (S j)).toList := by
  intro j hj
  rw [eGens_length] at hj
  apply imageList_of_tabN
  rw [eGens_getD hj, toTable_eq_tabN (prep_curtis (hL _ (List.getElem_mem hj))), hS j hj,
    List.getD_eq_getElem _ _ hj]

theorem hsU : ∀ j < 4, U.S j = CertificateChecks.KernelO8.AP.S ([0, 2, 4, 6].getD j 0) := by
  decide +kernel

theorem hsV0 : ∀ j < 7,
    V0.S j = CertificateChecks.KernelO8.AP.S ([0, 2, 3, 4, 5, 6, 7].getD j 0) := by
  decide +kernel

theorem hsV1 : ∀ j < 7,
    V1.S j = CertificateChecks.KernelO8.AP.S ([0, 1, 2, 3, 4, 5, 6].getD j 0) := by
  decide +kernel

theorem hsV2 : ∀ j < 7,
    V2.S j = CertificateChecks.KernelO8.AP.S ([0, 1, 2, 3, 4, 6, 7].getD j 0) := by
  decide +kernel

theorem hsP1 : ∀ j < 5, P1.S j = CertificateChecks.KernelO8.AP.S ([0, 1, 2, 4, 6].getD j 0) := by
  decide +kernel

theorem hsP3 : ∀ j < 5, P3.S j = CertificateChecks.KernelO8.AP.S ([0, 2, 3, 4, 6].getD j 0) := by
  decide +kernel

theorem hsP5 : ∀ j < 5, P5.S j = CertificateChecks.KernelO8.AP.S ([0, 2, 4, 5, 6].getD j 0) := by
  decide +kernel

theorem hsP7 : ∀ j < 5, P7.S j = CertificateChecks.KernelO8.AP.S ([0, 2, 4, 6, 7].getD j 0) := by
  decide +kernel

theorem hsP57 : ∀ j < 6,
    P57.S j = CertificateChecks.KernelO8.AP.S ([0, 2, 4, 5, 6, 7].getD j 0) := by
  decide +kernel

theorem hsP15 : ∀ j < 6,
    P15.S j = CertificateChecks.KernelO8.AP.S ([0, 1, 2, 4, 5, 6].getD j 0) := by
  decide +kernel

theorem hsP17 : ∀ j < 6,
    P17.S j = CertificateChecks.KernelO8.AP.S ([0, 1, 2, 4, 6, 7].getD j 0) := by
  decide +kernel

theorem chainU : ChainK 360 9 (eGens [0, 2, 4, 6]) dU (#v[0, 2, 4, 24, 8] : Vector (Fin 360) 5)
    U.S U.SI U.LR U.TR U.TRI 7 U.BP U.NS 24 :=
  ⟨by norm_num, by norm_num, by norm_num, eGens_img (by decide) hsU, by decide,
    by rw [eGens_length]; exact U.head, U.hl, by decide, U.hs⟩

theorem chainV0 : ChainK 360 9 (eGens [0, 2, 3, 4, 5, 6, 7]) dV0
    (#v[0, 2, 1, 4, 24, 8] : Vector (Fin 360) 6) V0.S V0.SI V0.LR V0.TR V0.TRI 12 V0.BP V0.NS 24 :=
  ⟨by norm_num, by norm_num, by norm_num, eGens_img (by decide) hsV0, by decide,
    by rw [eGens_length]; exact V0.head, V0.hl, by decide, V0.hs⟩

theorem chainV1 : ChainK 360 9 (eGens [0, 1, 2, 3, 4, 5, 6]) dV1
    (#v[0, 2, 1, 4, 24, 8, 9] : Vector (Fin 360) 7) V1.S V1.SI V1.LR V1.TR V1.TRI 14 V1.BP V1.NS 24 :=
  ⟨by norm_num, by norm_num, by norm_num, eGens_img (by decide) hsV1, by decide,
    by rw [eGens_length]; exact V1.head, V1.hl, by decide, V1.hs⟩

theorem chainV2 : ChainK 360 9 (eGens [0, 1, 2, 3, 4, 6, 7]) dV2
    (#v[0, 2, 1, 4, 24, 8] : Vector (Fin 360) 6) V2.S V2.SI V2.LR V2.TR V2.TRI 14 V2.BP V2.NS 24 :=
  ⟨by norm_num, by norm_num, by norm_num, eGens_img (by decide) hsV2, by decide,
    by rw [eGens_length]; exact V2.head, V2.hl, by decide, V2.hs⟩

theorem chainP1 : ChainK 360 9 (eGens [0, 1, 2, 4, 6]) dP1
    (#v[0, 2, 4, 24, 8] : Vector (Fin 360) 5) P1.S P1.SI P1.LR P1.TR P1.TRI 9 P1.BP P1.NS 24 :=
  ⟨by norm_num, by norm_num, by norm_num, eGens_img (by decide) hsP1, by decide,
    by rw [eGens_length]; exact P1.head, P1.hl, by decide, P1.hs⟩

theorem chainP3 : ChainK 360 9 (eGens [0, 2, 3, 4, 6]) dP3
    (#v[0, 2, 1, 4, 24, 8] : Vector (Fin 360) 6) P3.S P3.SI P3.LR P3.TR P3.TRI 8 P3.BP P3.NS 24 :=
  ⟨by norm_num, by norm_num, by norm_num, eGens_img (by decide) hsP3, by decide,
    by rw [eGens_length]; exact P3.head, P3.hl, by decide, P3.hs⟩

theorem chainP5 : ChainK 360 9 (eGens [0, 2, 4, 5, 6]) dP5
    (#v[0, 2, 4, 24, 8] : Vector (Fin 360) 5) P5.S P5.SI P5.LR P5.TR P5.TRI 8 P5.BP P5.NS 24 :=
  ⟨by norm_num, by norm_num, by norm_num, eGens_img (by decide) hsP5, by decide,
    by rw [eGens_length]; exact P5.head, P5.hl, by decide, P5.hs⟩

theorem chainP7 : ChainK 360 9 (eGens [0, 2, 4, 6, 7]) dP7
    (#v[0, 2, 4, 24, 8] : Vector (Fin 360) 5) P7.S P7.SI P7.LR P7.TR P7.TRI 8 P7.BP P7.NS 24 :=
  ⟨by norm_num, by norm_num, by norm_num, eGens_img (by decide) hsP7, by decide,
    by rw [eGens_length]; exact P7.head, P7.hl, by decide, P7.hs⟩

theorem chainP57 : ChainK 360 9 (eGens [0, 2, 4, 5, 6, 7]) dP57
    (#v[0, 2, 4, 24, 8] : Vector (Fin 360) 5) P57.S P57.SI P57.LR P57.TR P57.TRI 9 P57.BP P57.NS 24 :=
  ⟨by norm_num, by norm_num, by norm_num, eGens_img (by decide) hsP57, by decide,
    by rw [eGens_length]; exact P57.head, P57.hl, by decide, P57.hs⟩

theorem chainP15 : ChainK 360 9 (eGens [0, 1, 2, 4, 5, 6]) dP15
    (#v[0, 2, 4, 24, 8] : Vector (Fin 360) 5) P15.S P15.SI P15.LR P15.TR P15.TRI 10 P15.BP P15.NS 24 :=
  ⟨by norm_num, by norm_num, by norm_num, eGens_img (by decide) hsP15, by decide,
    by rw [eGens_length]; exact P15.head, P15.hl, by decide, P15.hs⟩

theorem chainP17 : ChainK 360 9 (eGens [0, 1, 2, 4, 6, 7]) dP17
    (#v[0, 2, 4, 24, 8] : Vector (Fin 360) 5) P17.S P17.SI P17.LR P17.TR P17.TRI 10 P17.BP P17.NS 24 :=
  ⟨by norm_num, by norm_num, by norm_num, eGens_img (by decide) hsP17, by decide,
    by rw [eGens_length]; exact P17.head, P17.hl, by decide, P17.hs⟩

theorem ordU : ordK U.LR 5 = 4096 := by decide +kernel
theorem ordV0 : ordK V0.LR 6 = 1290240 := by decide +kernel
theorem ordV1 : ordK V1.LR 7 = 1290240 := by decide +kernel
theorem ordV2 : ordK V2.LR 6 = 1290240 := by decide +kernel
theorem ordP1 : ordK P1.LR 5 = 12288 := by decide +kernel
theorem ordP3 : ordK P3.LR 6 = 12288 := by decide +kernel
theorem ordP5 : ordK P5.LR 5 = 12288 := by decide +kernel
theorem ordP7 : ordK P7.LR 5 = 12288 := by decide +kernel
theorem ordP57 : ordK P57.LR 5 = 36864 := by decide +kernel
theorem ordP15 : ordK P15.LR 5 = 36864 := by decide +kernel
theorem ordP17 : ordK P17.LR 5 = 36864 := by decide +kernel

theorem eUQ_ok : (eUQ ()).check = true ∧ (eUQ ()).orderCertificate = 4096 := by
  unfold eUQ
  rw [← ordU]
  exact chainK_check (by norm_num) (by decide) chainU

theorem eV0Q_ok : (eV0Q ()).check = true ∧ (eV0Q ()).orderCertificate = 1290240 := by
  unfold eV0Q
  rw [← ordV0]
  exact chainK_check (by norm_num) (by decide) chainV0

theorem eV1Q_ok : (eV1Q ()).check = true ∧ (eV1Q ()).orderCertificate = 1290240 := by
  unfold eV1Q
  rw [← ordV1]
  exact chainK_check (by norm_num) (by decide) chainV1

theorem eV2Q_ok : (eV2Q ()).check = true ∧ (eV2Q ()).orderCertificate = 1290240 := by
  unfold eV2Q
  rw [← ordV2]
  exact chainK_check (by norm_num) (by decide) chainV2

theorem eP1Q_ok : (eP1Q ()).check = true ∧ (eP1Q ()).orderCertificate = 12288 := by
  unfold eP1Q
  rw [← ordP1]
  exact chainK_check (by norm_num) (by decide) chainP1

theorem eP3Q_ok : (eP3Q ()).check = true ∧ (eP3Q ()).orderCertificate = 12288 := by
  unfold eP3Q
  rw [← ordP3]
  exact chainK_check (by norm_num) (by decide) chainP3

theorem eP5Q_ok : (eP5Q ()).check = true ∧ (eP5Q ()).orderCertificate = 12288 := by
  unfold eP5Q
  rw [← ordP5]
  exact chainK_check (by norm_num) (by decide) chainP5

theorem eP7Q_ok : (eP7Q ()).check = true ∧ (eP7Q ()).orderCertificate = 12288 := by
  unfold eP7Q
  rw [← ordP7]
  exact chainK_check (by norm_num) (by decide) chainP7

theorem eP57Q_ok : (eP57Q ()).check = true ∧ (eP57Q ()).orderCertificate = 36864 := by
  unfold eP57Q
  rw [← ordP57]
  exact chainK_check (by norm_num) (by decide) chainP57

theorem eP15Q_ok : (eP15Q ()).check = true ∧ (eP15Q ()).orderCertificate = 36864 := by
  unfold eP15Q
  rw [← ordP15]
  exact chainK_check (by norm_num) (by decide) chainP15

theorem eP17Q_ok : (eP17Q ()).check = true ∧ (eP17Q ()).orderCertificate = 36864 := by
  unfold eP17Q
  rw [← ordP17]
  exact chainK_check (by norm_num) (by decide) chainP17

end CertificateChecks.KernelAE6CertE

end
