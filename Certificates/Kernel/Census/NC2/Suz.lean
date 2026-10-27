module

public import Certificates.Kernel.LocalComp.LaySeeds
public import Certificates.Kernel.LocalComp.LaySnapsLive
public import CFSG.Certificates.Kernel.Common.JsonGz
public import CFSG.Certificates.Kernel.Common.Each
public import CFSG.Certificates.Kernel.Common.ForallChunks
import CFSG.Certificates.Kernel.Common.Repo
import all CFSG.Blueprint.NativeSporadic

set_option maxRecDepth 400000

#lay_seeds CertificateChecks.KernelNC2.Suz.L 3 64
  CFSG.Blueprint.NativeSporadic.SuzSeed1 CFSG.Blueprint.NativeSporadic.SuzSeed2

#kc_repo #lay_snaps_live CertificateChecks.KernelNC2.Suz.P 3 64 CertificateChecks.KernelNC2.Suz.L.A
  CertificateChecks.KernelNC2.Suz.L.B "Certificates/Kernel/Census/NC2/data/suz.json.gz" 40646
  2160765264640993387

#kc_repo #kc_json_gz CertificateChecks.KernelNC2.Suz.D
  "Certificates/Kernel/Census/NC2/data/suz.json.gz" 40646 2160765264640993387
  (a : Nat) (tests : List Nat) (oddExp : Nat) (extra : List Nat) (sq : List Nat)
  (cj : List (List Nat)) (sig : List Nat) (sigma : List Nat) (tau : List Nat)
  (pairs : List (Nat × Nat))

public section

namespace CertificateChecks.KernelNC2.Suz

open CFSG.KC.NC2L

@[expose] noncomputable def data : NC2LData :=
  { a := D.a, tests := D.tests, oddExp := D.oddExp, extra := D.extra, sq := D.sq, cj := D.cj,
    sig := D.sig, sigma := D.sigma, tau := D.tau, pairs := D.pairs }

@[expose] noncomputable def chunkOK (i : Nat) : Bool :=
  liveL L.lay (P.CL.getD i ⟨0, [], []⟩) (P.SL.getD i []) (P.SL.getD (i + 1) [])

theorem m_eq : P.m = 13 := rfl

#kc_each CertificateChecks.KernelNC2.Suz.chunkOK 0 13

#kc_forall_chunks chain (fun i => chunkOK i = true) 13 CertificateChecks.KernelNC2.Suz.chunkOK 1

theorem nc2_K : nc2L L.lay (P.SL.getD P.m []) data = true := by decide +kernel

theorem neg_seeds : (!liveL L.lay P.C0 [L.B, L.A] P.S1) = true := by decide +kernel

theorem neg_sq : (!nc2L L.lay (P.SL.getD P.m [])
    { data with sq := (data.sq.head! ^^^ 2) :: data.sq.tail }) = true := by
  decide +kernel

theorem neg_cj : (!nc2L L.lay (P.SL.getD P.m [])
    { data with cj := ((data.cj.head!.head! ^^^ 2) :: data.cj.head!.tail) :: data.cj.tail }) =
      true := by
  decide +kernel

theorem neg_sigma : (!nc2L L.lay (P.SL.getD P.m [])
    { data with sigma := data.sigma.head! :: data.sigma.tail.tail ++ [data.sigma.head!] }) =
      true := by
  decide +kernel

theorem neg_pairs : (!nc2L L.lay (P.SL.getD P.m []) { data with pairs := data.pairs.tail }) =
    true := by
  decide +kernel

theorem neg_exp : (!nc2L L.lay (P.SL.getD P.m []) { data with oddExp := data.oddExp + 2 }) =
    true := by
  decide +kernel

theorem neg_extra : (!nc2L L.lay (P.SL.getD P.m []) { data with extra := [5] }) = true := by
  decide +kernel

end CertificateChecks.KernelNC2.Suz

end
