module

public import Certificates.Data.E6Heart
public meta import Certificates.Data.E6Heart
import all Certificates.Data.E6Heart
import Certificates.Kernel.E6Heart.Twin
import Certificates.Kernel.E6Heart.Mask
import Certificates.Kernel.E6Heart.ZDot

public section

open Certificates.E6Heart

namespace CertificateChecks.Batch712501

open Certificates.E6Heart

open CertificateChecks.E6HeartK

set_option maxHeartbeats 0

private theorem v_ok : vOk = true := by decide +kernel

private theorem adjv_ok : adjOkV = true := by decide +kernel

private theorem adj_ok : adjOk = true := adjOk_of v_ok adjv_ok

private theorem zv_ok : zOkV = true := by decide +kernel

private theorem z_ok : zOk = true := zOk_of v_ok zv_ok

private theorem sym_ok : symOk = true := by decide +kernel

private theorem rows_ok : rowsOk = true := by decide +kernel

private theorem heart_roots : rootsOk () = true := by decide +kernel

private theorem heart_rad : radOk () = true := by decide +kernel

private theorem heart_good0 : (List.range' 0 30).all (fun t => t == 0 || goodAtM t) = true := by
  decide +kernel

private theorem heart_good1 : (List.range' 30 30).all (fun t => t == 0 || goodAtM t) = true := by
  decide +kernel

private theorem heart_good2 : (List.range' 60 30).all (fun t => t == 0 || goodAtM t) = true := by
  decide +kernel

private theorem heart_good3 : (List.range' 90 30).all (fun t => t == 0 || goodAtM t) = true := by
  decide +kernel

private theorem heart_good4 : (List.range' 120 30).all (fun t => t == 0 || goodAtM t) = true := by
  decide +kernel

private theorem heart_good5 : (List.range' 150 30).all (fun t => t == 0 || goodAtM t) = true := by
  decide +kernel

private theorem heart_good6 : (List.range' 180 30).all (fun t => t == 0 || goodAtM t) = true := by
  decide +kernel

private theorem heart_good7 : (List.range' 210 30).all (fun t => t == 0 || goodAtM t) = true := by
  decide +kernel

private theorem heart_good8 : (List.range' 240 3).all (fun t => t == 0 || goodAtM t) = true := by
  decide +kernel

private theorem heart_good : (List.range 243).all (fun t => t == 0 || goodAtM t) = true := by
  have H : ∀ a n, (List.range' a n).all (fun t => t == 0 || goodAtM t) = true →
      ∀ t, a ≤ t → t < a + n → (t == 0 || goodAtM t) = true := fun a n h t h1 h2 =>
    List.all_eq_true.1 h t (List.mem_range'_1.2 ⟨h1, h2⟩)
  rw [List.all_eq_true]
  intro t ht
  rw [List.mem_range] at ht
  rcases (by omega : t < 30 ∨ (30 ≤ t ∧ t < 60) ∨ (60 ≤ t ∧ t < 90) ∨ (90 ≤ t ∧ t < 120) ∨
      (120 ≤ t ∧ t < 150) ∨ (150 ≤ t ∧ t < 180) ∨ (180 ≤ t ∧ t < 210) ∨ (210 ≤ t ∧ t < 240) ∨
      240 ≤ t) with h | h | h | h | h | h | h | h | h
  · exact H 0 30 heart_good0 t (by omega) (by omega)
  · exact H 30 30 heart_good1 t (by omega) (by omega)
  · exact H 60 30 heart_good2 t (by omega) (by omega)
  · exact H 90 30 heart_good3 t (by omega) (by omega)
  · exact H 120 30 heart_good4 t (by omega) (by omega)
  · exact H 150 30 heart_good5 t (by omega) (by omega)
  · exact H 180 30 heart_good6 t (by omega) (by omega)
  · exact H 210 30 heart_good7 t (by omega) (by omega)
  · exact H 240 3 heart_good8 t (by omega) (by omega)

private theorem check_m : checkM = true := by
  rw [checkM, heart_roots, heart_rad, heart_good]
  decide +kernel

private theorem e6_heart_check_0 : check () = true := by
  rw [check_eq adj_ok z_ok, checkK_eq adj_ok sym_ok rows_ok]
  exact check_m

end CertificateChecks.Batch712501

namespace Certificates

open Certificates.E6Heart in
theorem certificate712501 : check () = true := by
  exact CertificateChecks.Batch712501.e6_heart_check_0

end Certificates
