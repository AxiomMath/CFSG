module

public import Certificates.Data.Th687.MFactsD
import Certificates.Kernel.Th.Fam.C687008
import Certificates.Kernel.Th.Fam.Ctx

public section

namespace Certificates

open CFSG.KC.Th.Expr CFSG.Sporadic.Th.Native CFSG.Sporadic.Th.Max3
open CFSG.Sporadic.Th.Recog.MFactsBData CFSG.Sporadic.Th.Recog.MFactsDData
open CertificateChecks.KernelTh.Fam

private theorem comm_eq (e : TE) (k : Fin 512) :
    eqRows (mulRows e.rows (rowsNfAt k)) (mulRows (rowsNfAt k) e.rows) =
      Nat.beq (thK.mul (e.pk thK) ((TE.nf k).pk thK)) (thK.mul ((TE.nf k).pk thK) (e.pk thK)) := by
  kernel_exact eqRows_eq_beq thCtx (.mul e (.nf k)) (.mul (.nf k) e)

private theorem sq_eq (k : Fin 512) :
    eqRows (mulRows (rowsNfAt k) (rowsNfAt k)) idRows =
      Nat.beq ((TE.mul (.nf k) (.nf k)).pk thK) (TE.one.pk thK) := by
  kernel_exact eqRows_eq_beq thCtx (.mul (.nf k) (.nf k)) .one

private theorem commFilter_eq (e : TE) : commFilter e.rows = commL (e.pk thK) := by
  unfold commFilter commL
  exact List.filter_congr fun k _ => comm_eq e k

private theorem all_eq (e : TE) :
    ((commFilter e.rows).all fun k =>
      decide (k.val ≤ 1) || !eqRows (mulRows (rowsNfAt k) (rowsNfAt k)) idRows) =
      invL (commL (e.pk thK)) := by
  rw [commFilter_eq e]
  unfold invL
  simp only [sq_eq]

private theorem check0 : checkT3687008 () = true :=
  by kernel_exact (all_eq w12T).trans ok687008a

private theorem check1 : checkT333687008 () = true :=
  by kernel_exact (all_eq w1T).trans ok687008b

private theorem check2 : (centSList ()).length = 8 := by
  kernel_exact (congrArg List.length (commFilter_eq (wjT 5))).trans
    (Nat.eq_of_beq_eq_true ok687008c)

open CFSG.Sporadic.Th.Native CFSG.Sporadic.Th.Max3 in
open CFSG.Sporadic.Th.Recog.MFactsDData in
theorem certificate687008 :
    checkT3687008 () = true ∧
      checkT333687008 () = true ∧
      (centSList ()).length = 8 :=
  ⟨check0, check1, check2⟩

end Certificates
