module

public import Certificates.Kernel.Cert690.PglEnum
public import Certificates.Kernel.Cert690.PglF
public import Certificates.Kernel.Cert690.PglF10A
public import Certificates.Kernel.Cert690.PglF10B
public import Certificates.Kernel.Cert690.PglF10C
public import Certificates.Kernel.Cert690.PglF11A
public import Certificates.Kernel.Cert690.PglF11B
public import CFSG.Certificates.Kernel.Cert690.PglSound
public import CFSG.Certificates.Kernel.Cert690.EnumSound

public section

namespace CertificateChecks.KernelC690.Pgl

open CFSG.KC.C690 CFSG.GF2Type.Smith1979W3.Cert690

theorem ix : K.Nodup ∧ ∀ c, (idxT S).find c K.length = K.idxOf c := find_idxT_eq_idxOf ixK

theorem ix0 : K0.Nodup ∧ ∀ c, (idxT S0).find c K0.length = K0.idxOf c := find_idxT_eq_idxOf ixK0

theorem enumK_eq : enumData kPGLGens = (K.toArray, par.toArray) :=
  enumData_of_bfsOK ix.2 bfsK (by rw [lenK]; decide)

theorem enumK0_eq : enumData kPGL0Gens = (K0.toArray, par0.toArray) :=
  enumData_of_bfsOK ix0.2 bfsK0 (by rw [lenK0]; decide)

theorem f10 : pglF10K K.toArray (invsL K).toArray = true := by
  unfold pglF10K
  rw [List.all_eq_true]
  intro e he
  obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem he
  have hlen : f10Vecs.length = 21 := by decide
  have e' : f10At K.toArray (invsL K).toArray f10Vecs[k] = f10I k := by
    unfold f10I
    rw [List.getD_eq_getElem _ _ hk]
  rw [e']
  rw [hlen] at hk
  interval_cases k
  exacts [f10I0, f10I1, f10I2, f10I3, f10I4, f10I5, f10I6, f10I7, f10I8, f10I9, f10I10, f10I11,
    f10I12, f10I13, f10I14, f10I15, f10I16, f10I17, f10I18, f10I19, f10I20]

theorem f11 : pglF11K K.toArray K0.toArray (outersL K K0).toArray = true := by
  unfold pglF11K
  rw [fOut, Bool.true_and, List.toList_toArray, List.all_eq_true]
  intro u hu
  obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hu
  have hlen : (outersL K K0).length = 28 := by decide +kernel
  have e' : f11At K.toArray (outersL K K0)[k] = f11I k := by
    unfold f11I
    rw [List.getD_eq_getElem _ _ hk]
  rw [e']
  rw [hlen] at hk
  interval_cases k
  exacts [f11I0, f11I1, f11I2, f11I3, f11I4, f11I5, f11I6, f11I7, f11I8, f11I9, f11I10, f11I11,
    f11I12, f11I13, f11I14, f11I15, f11I16, f11I17, f11I18, f11I19, f11I20, f11I21, f11I22,
    f11I23, f11I24, f11I25, f11I26, f11I27]

theorem pglFactsP : pglFactsCheck () = true := by
  have hel := pgl_elems enumK_eq enumK0_eq
  have hel0 := pgl_elems0 enumK_eq enumK0_eq
  have hnd : (pglData ()).elems.toList.Nodup := by rw [hel]; exact ix.1
  have e1 : enumOK kPGLGens (pglData ()).elems (pglData ()).par = true := by
    rw [hel, pgl_par enumK_eq enumK0_eq]
    exact enumOK_of ixK (by rw [lenK]; norm_num) headK enumK.1 enumK.2.1 enumK.2.2
  have e2 : enumOK kPGL0Gens (pglData ()).elems0 (pglData ()).par0 = true := by
    rw [hel0, pgl_par0 enumK_eq enumK0_eq]
    exact enumOK_of ixK0 (by rw [lenK0]; norm_num) headK0 enumK0.1 enumK0.2.1 enumK0.2.2
  have hf1 : pglF1Of (pglData ()) = true := by
    rw [pglF1Of_eq, e1, e2, hel, hel0, pgl_invs enumK_eq enumK0_eq,
      pgl_invs0 enumK_eq enumK0_eq, f1]
    rfl
  have hf2 : pglF2Of (pglData ()) = true := f2
  have hf3 : pglF3Of (pglData ()) = true := by
    unfold pglF3Of
    rw [hel, hel0, List.size_toArray, List.size_toArray, lenK, lenK0]
    rfl
  have hf4 : pglF4Of (pglData ()) = true := by
    rw [pglF4Of_eq _ (pgl_invMap enumK_eq enumK0_eq ix.1 · 0), hel, hel0,
      pgl_invs enumK_eq enumK0_eq, pgl_commWit enumK_eq enumK0_eq]
    exact f4
  have hf5 : pglF5Of (pglData ()) = true := by
    rw [pglF5Of_eq]
    exact f5
  have hf6 : pglF6Of (pglData ()) = true := by rw [pglF6Of_eq]; exact f6
  have hf7 : pglF7Of (pglData ()) = true := by rw [pglF7Of_eq, hel, hel0]; exact f7
  have hf8 : pglF8Of (pglData ()) = true := by rw [pglF8Of_eq, hel0]; exact f8
  have hf9 : pglF9Of (pglData ()) = true := by
    rw [pglF9Of_eq, hel, pgl_w9 enumK_eq enumK0_eq]
    exact f9
  have hf10 : pglF10Of (pglData ()) = true := by
    rw [pglF10Of_eq _ hnd, hel, pgl_invs enumK_eq enumK0_eq]
    exact f10
  have hf11 : pglF11Of (pglData ()) = true := by
    rw [pglF11Of_eq _ hnd, hel, hel0, pgl_outers enumK_eq enumK0_eq]
    exact f11
  have hf12 : pglF12Of (pglData ()) = true := by
    rw [pglF12Of_eq, hel, hel0, pgl_invs enumK_eq enumK0_eq,
      pgl_involutions enumK_eq enumK0_eq, pgl_outers enumK_eq enumK0_eq,
      pgl_w12 enumK_eq enumK0_eq]
    exact f12
  have hf13 : pglF13Of (pglData ()) = true := by rw [pglF13Of_eq, hel, hel0]; exact f13
  unfold pglFactsCheck
  simp only [hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8, hf9, hf10, hf11, hf12, hf13, Bool.and_self]

end CertificateChecks.KernelC690.Pgl

end
