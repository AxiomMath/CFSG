module

public import Certificates.Data.Th687.MFactsB
import Certificates.Kernel.Th.Fam.C687012
import Certificates.Kernel.Th.Fam.Ctx

public section

namespace Certificates

open CFSG.KC.Th.Expr CFSG.Sporadic.Th.Native CFSG.Sporadic.Th.Max3
open CFSG.Sporadic.Th.Recog.MFactsBData CertificateChecks.KernelTh.Fam

private theorem centT_eq (k : Fin 512) :
    eqRows (mulRows (rowsT ()) (rowsNfAt k)) (mulRows (rowsNfAt k) (rowsT ())) = centP k := by
  kernel_exact eqRows_eq_beq thCtx (.mul tT (.nf k)) (.mul (.nf k) tT)

private theorem nf_comm_eq (k k' : Fin 512) :
    eqRows (mulRows (rowsNfAt k) (rowsNfAt k')) (mulRows (rowsNfAt k') (rowsNfAt k)) =
      Nat.beq ((TE.mul (.nf k) (.nf k')).pk thK) ((TE.mul (.nf k') (.nf k)).pk thK) := by
  kernel_exact eqRows_eq_beq thCtx (.mul (.nf k) (.nf k')) (.mul (.nf k') (.nf k))

private theorem centTList_eq : centTList () = centL := by
  unfold centTList commFilter centL
  exact List.filter_congr fun k _ => centT_eq k

private theorem centTCenter_eq : centTCenter () = centCK := by
  unfold centTCenter centCK
  rw [centTList_eq]
  simp only [nf_comm_eq]

open CFSG.Sporadic.Th.Native CFSG.Sporadic.Th.Max3 in
open CFSG.Sporadic.Th.Recog.MFactsBData in
theorem certificate687012 :
    (CFSG.Sporadic.Th.Recog.MFactsBData.centTList ()).length = 32 ∧
      CFSG.Sporadic.Th.Recog.MFactsBData.centTCenter () = true := by
  refine ⟨?_, ?_⟩
  · rw [centTList_eq]
    kernel_exact Nat.eq_of_beq_eq_true ok687012a
  · rw [centTCenter_eq]
    kernel_exact ok687012b

end Certificates
