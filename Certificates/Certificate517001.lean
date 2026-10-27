module

public import Certificates.Data.S7M12
import CFSG.Certificates.Kernel.PermCent.S7M12CSound
import Certificates.Kernel.PermCent.K517001
public import Certificates.Data.Kernel.PermCent.CV
import CFSG.Certificates.Kernel.PermCent.S7Q8MapSound

public section

open CFSG.Blueprint CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf
  CFSG.Certificates.Kernel.PkCV CFSG.Certificates.Kernel.PkCV.S7M12C Certificates.S5Rows
  Certificates.S5RowsM12 Certificates.S7Q8 Certificates.S7M12 CFSG.Sporadic.Mathieu

namespace Certificates

open Certificates.S7M12 in
theorem certificate517001 : m12S7Basic () = true ∧ m12S7Class1 () = true ∧ m12S7Class2 () = true ∧
    m12S7Norm () = true ∧ m12S7Q8 () = true ∧ m12S7Edge () = true := by
  have hs := NativeSporadic.M12.subtype_injective
  have he : Function.Injective (evHom 12) := ev_injective
  have hi1 : NativeSporadic.M12.subtype i1 = evHom 12 (eC 27) := sub_eltM (by norm_num)
  have hj1 : NativeSporadic.M12.subtype j1 = evHom 12 (eC 48) := sub_eltM (by norm_num)
  have hi2 : NativeSporadic.M12.subtype i2 = evHom 12 (eC 4) := sub_eltM (by norm_num)
  have hj2 : NativeSporadic.M12.subtype j2 = evHom 12 (eC 38) := sub_eltM (by norm_num)
  have hz : NativeSporadic.M12.subtype (M12Model.eltM 22) = evHom 12 (eC 22) :=
    sub_eltM (by norm_num)
  have hq (a b : NativeSporadic.M12) (c d : CV 12) (ha : NativeSporadic.M12.subtype a = evHom 12 c)
      (hb : NativeSporadic.M12.subtype b = evHom 12 d) : q8RelB a b = q8RelB c d := by
    rw [← q8RelB_map _ hs, ha, hb, q8RelB_map _ he]
  have hsq (a : NativeSporadic.M12) (c : CV 12) (ha : NativeSporadic.M12.subtype a = evHom 12 c) :
      decide (a * a = M12Model.eltM 22) = decide (c * c = eC 22) := by
    rw [decide_eq_decide, ← hs.eq_iff, map_mul, ha, hz, ← map_mul, he.eq_iff]
  have hspan : (q8Span i2 j2).map NativeSporadic.M12.subtype =
      (q8Span (eC 4) (eC 38)).map (evHom 12) := by
    rw [← q8Span_map, hi2, hj2, q8Span_map]
  have hfp : ((q8Span i2 j2).all fun x => M12Model.fp x != M12Model.fp i1) =
      (q8Span (eC 4) (eC 38)).all fun x => fpC x != fpC (eC 27) := by
    calc ((q8Span i2 j2).all fun x => M12Model.fp x != M12Model.fp i1)
        = ((q8Span i2 j2).map NativeSporadic.M12.subtype).all fun y =>
            M12Model.fixPts y != M12Model.fixPts (NativeSporadic.M12.subtype i1) := by
          rw [List.all_map]
          rfl
      _ = ((q8Span (eC 4) (eC 38)).map (evHom 12)).all fun y =>
            M12Model.fixPts y != M12Model.fixPts (evHom 12 (eC 27)) := by
          rw [hspan, hi1]
      _ = _ := by
          rw [List.all_map]
          simp only [Function.comp_def, evHom_apply, fixPts_ev]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [m12S7Basic, hq i1 j1 _ _ hi1 hj1, hq i2 j2 _ _ hi2 hj2, hsq i1 _ hi1, hsq i2 _ hi2, hfp]
    exact K517001.k517001_basic
  · rw [m12S7Class1, ← classCheck_map _ hs, hi1, hj1, sylowL_map, conjL_map,
      classCheck_map _ he]
    exact K517001.k517001_class1
  · rw [m12S7Class2, ← classCheck_map _ hs, hi2, hj2, sylowL_map, conjL_map,
      classCheck_map _ he]
    exact K517001.k517001_class2
  · have h1 : normAllB i1 j1 (czL ()) = normAllB (eC 27) (eC 48) CZc := by
      rw [← normAllB_map _ hs, hi1, hj1, czL_map, normAllB_map _ he]
    have h2 : normAllB i2 j2 (czL ()) = normAllB (eC 4) (eC 38) CZc := by
      rw [← normAllB_map _ hs, hi2, hj2, czL_map, normAllB_map _ he]
    simp only [m12S7Norm, h1, h2, K517001.k517001_norm1, K517001.k517001_norm2, Bool.and_self]
  · have h1 : q8InCheck (sylowL ()) i1 j1 i2 j2 = q8InCheck SLc (eC 27) (eC 48) (eC 4) (eC 38) := by
      rw [← q8InCheck_map _ hs, hi1, hj1, hi2, hj2, sylowL_map, q8InCheck_map _ he]
    have h2 : q8InCheck (czL ()) i1 j1 i2 j2 = q8InCheck CZc (eC 27) (eC 48) (eC 4) (eC 38) := by
      rw [← q8InCheck_map _ hs, hi1, hj1, hi2, hj2, czL_map, q8InCheck_map _ he]
    simp only [m12S7Q8, h1, h2, ← q8InCheck_filter_ord4 SLc, ← q8InCheck_filter_ord4 CZc,
      K517001.k517001_q8S, K517001.k517001_q8CZ, Bool.and_self]
  · have h1 : edgeB i1 j1 i2 j2 (edgeE ()) = edgeB (eC 27) (eC 48) (eC 4) (eC 38) Ec := by
      rw [← edgeB_map _ hs, hi1, hj1, hi2, hj2, sub_edgeE, edgeB_map _ he]
    have hE : [edgeE ()].map NativeSporadic.M12.subtype = [Ec].map (evHom 12) := by
      rw [List.map_singleton, List.map_singleton, sub_edgeE]
    have h2 : factB i1 j1 i2 j2 [edgeE ()] m12a (factAL ()) =
        factB (eC 27) (eC 48) (eC 4) (eC 38) [Ec] Ac FAc := by
      rw [← factB_map _ hs, hi1, hj1, hi2, hj2, hE, sub_a, factAL_map, factB_map _ he]
    have h3 : factB i1 j1 i2 j2 [edgeE ()] m12b (factBL ()) =
        factB (eC 27) (eC 48) (eC 4) (eC 38) [Ec] Bc FBc := by
      rw [← factB_map _ hs, hi1, hj1, hi2, hj2, hE, sub_b, factBL_map, factB_map _ he]
    change (edgeB i1 j1 i2 j2 (edgeE ()) && factB i1 j1 i2 j2 [edgeE ()] m12a (factAL ()) &&
      factB i1 j1 i2 j2 [edgeE ()] m12b (factBL ())) = true
    rw [h1, h2, h3]
    exact K517001.k517001_edge

end Certificates
