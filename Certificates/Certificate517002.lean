module

public import Certificates.Data.S7U33
import CFSG.Certificates.Kernel.PermCent.CVSound
import CFSG.Certificates.Kernel.PermCent.S7Q8MapSound
import Certificates.Kernel.PermCent.K517002
public import Certificates.Data.Kernel.PermCent.CV

open CFSG.Certificates.Kernel.PkCV CFSG.Certificates.Kernel.PkCV.S7U33C Certificates.S5Rows
  Certificates.S5RowsU33 Certificates.S7Q8 Certificates.S7U33 CFSG.GH74.KGroups
  CFSG.Sporadic.Schreier

namespace CertificateChecks.C517002

theorem he : Function.Injective (evHom 28) := ev_injective

theorem evHom_ev (c : CV 28) : evHom 28 c = ev c := rfl

theorem cOf_eq (σ : Equiv.Perm (Fin 28)) : σ = evHom 28 (cOf σ) := eq_ev_cOf σ

theorem sg_eq : U33.sg0 = evHom 28 SG := cOf_eq _

theorem pa_eq : U33.pa = evHom 28 PA := cOf_eq _

theorem pb_eq : U33.pb = evHom 28 PB := cOf_eq _

theorem gensA_eq : gensA = gensC.map (evHom 28) := by
  simp only [gensA, gensC, List.map_cons, List.map_nil, map_inv, ← cOf_eq]

theorem wA_eq (w : List ℕ) : wA w = evHom 28 (wAC w) := by
  rw [wA, tab_eq, wAC, map_list_prod, List.map_map]
  congr 1
  refine List.map_congr_left fun k _ => ?_
  rw [Function.comp_apply, gensA_eq, ← map_one (evHom 28), List.getD_map]

theorem i1_eq : i1 = evHom 28 I1 := wA_eq _
theorem j1_eq : j1 = evHom 28 J1 := wA_eq _
theorem i2_eq : i2 = evHom 28 I2 := wA_eq _
theorem j2_eq : j2 = evHom 28 J2 := wA_eq _

theorem sylowA_eq : sylowA () = SC.map (evHom 28) := by
  rw [sylowA, elemsT_eq_elemsC, SC]
  rfl

theorem elemsA_eq : elemsA () = AC.map (evHom 28) := by
  rw [elemsA, elemsT_eq_elemsC, AC]
  rfl

theorem inQP_eq (c : CV 28) : inQP (evHom 28 c) = siftC U33.QP c 0 := sift_ev U33.QP c 0

theorem czA_eq : czA () = CZC.map (evHom 28) := by
  simp only [czA, elemsA_eq, List.filter_map, CZC]
  refine congrArg (List.map _) (List.filter_congr fun x _ => ?_)
  simp only [Function.comp_apply, i1_eq, ← map_mul, he.eq_iff, eq22C_eq]

theorem factPa_eq : factPa () = FPa.map (evHom 28) := by
  simp only [factPa, FPa, List.map_cons, List.map_nil, map_inv, wA_eq, ← sg_eq]

theorem factPb_eq : factPb () = FPb.map (evHom 28) := by
  simp only [factPb, FPb, List.map_cons, List.map_nil, map_inv, wA_eq, ← sg_eq]

theorem sq_eq : decide (evHom 28 I2 * evHom 28 I2 = evHom 28 I1 * evHom 28 I1) =
    decide (I2 * I2 = I1 * I1) := by
  rw [decide_eq_decide, ← map_mul, ← map_mul, he.eq_iff]

end CertificateChecks.C517002

public section

namespace Certificates

open CertificateChecks.C517002

open Certificates.S7U33 in
theorem certificate517002 : u33S7Basic () = true ∧ u33S7Class1 () = true ∧ u33S7Class2 () = true ∧
    u33S7Norm () = true ∧ u33S7Q8 () = true ∧ u33S7Edge () = true := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [u33S7Basic, i1_eq, j1_eq, i2_eq, j2_eq, q8RelB_map _ he, q8RelB_map _ he, inQP_eq,
      inQP_eq, inQP_eq, inQP_eq, sq_eq]
    exact K517002.k517002_basic
  · rw [u33S7Class1, i1_eq, j1_eq, sylowA_eq, elemsA_eq, classCheck_map _ he]
    exact K517002.k517002_class1
  · rw [u33S7Class2, i2_eq, j2_eq, sylowA_eq, elemsA_eq, classCheck_map _ he]
    exact K517002.k517002_class2
  · have h := K517002.k517002_normS
    rw [Bool.and_eq_true] at h
    simp only [u33S7Norm, czA_eq, sylowA_eq, i1_eq, j1_eq, i2_eq, j2_eq, normAllB_map _ he,
      K517002.k517002_norm1, K517002.k517002_norm2, h.1, h.2, Bool.and_self]
  · simp only [u33S7Q8, czA_eq, sylowA_eq, i1_eq, j1_eq, i2_eq, j2_eq, q8InCheck_map _ he,
      ← q8InCheck_filter_ord4 SC, ← q8InCheck_filter_ord4 CZC, K517002.k517002_q8S,
      K517002.k517002_q8CZ, Bool.and_self]
  · have hE : [U33.sg0] = [SG].map (evHom 28) := by
      rw [List.map_singleton, ← sg_eq]
    rw [u33S7Edge, i1_eq, j1_eq, i2_eq, j2_eq, factPa_eq, factPb_eq, hE, sg_eq, pa_eq, pb_eq,
      edgeB_map _ he, factB_map _ he, factB_map _ he, factB_map _ he]
    exact K517002.k517002_edge

end Certificates
