module

public import Certificates.Data.Kernel.Co2Syl
import CFSG.Certificates.Kernel.Common.JsonGz
import CFSG.Certificates.Kernel.Common.Repo

public section

#kc_repo #kc_json_gz CertificateChecks.KernelSpor.Co2Syl
  "Certificates/Kernel/Co2Syl/data/small.json.gz" 14387 3736159505773733380
  (LT : List Nat) (RW : Array (List Nat)) (REP : List Nat)
  (GL1 : List Nat) (N1 : Nat) (B1 : Nat) (Bi1 : Nat) (MI1 : List Nat)
  (GL3 : List Nat) (N3 : Nat) (B3 : Nat) (Bi3 : Nat) (MI3 : List Nat)
  (GL4 : List Nat) (N4 : Nat) (B4 : Nat) (Bi4 : Nat) (MI4 : List Nat)
  (GL5 : List Nat) (N5 : Nat) (B5 : Nat) (Bi5 : Nat) (MI5 : List Nat)
  (GL6 : List Nat) (N6 : Nat) (B6 : Nat) (Bi6 : Nat) (MI6 : List Nat) (WA6 : Nat) (WB6 : Nat)
  (GL8 : List Nat) (N8 : Nat) (B8 : Nat) (Bi8 : Nat) (MI8 : List Nat) (WA8 : Nat) (WB8 : Nat)

namespace CertificateChecks.KernelSpor.Co2Syl

open CFSG.KC.Co2InvS

@[expose] noncomputable def lAt (L : List Nat) : Nat → Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun _ => nat_lit 0)
    (fun a _ f j => Nat.rec (motive := fun _ => Nat) a (fun i _ => f i) j) L

@[expose] noncomputable def G1 (j : Nat) : Nat := lAt GL1 j
@[expose] noncomputable def G3 (j : Nat) : Nat := lAt GL3 j
@[expose] noncomputable def G4 (j : Nat) : Nat := lAt GL4 j
@[expose] noncomputable def G5 (j : Nat) : Nat := lAt GL5 j
@[expose] noncomputable def G6 (j : Nat) : Nat := lAt GL6 j
@[expose] noncomputable def G8 (j : Nat) : Nat := lAt GL8 j

@[expose] noncomputable def RP (i : Nat) : Nat := lAt REP i

@[expose] noncomputable def wordK (w : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat) IDP (fun l _ acc => mulV (lAt LT l) acc) w

end CertificateChecks.KernelSpor.Co2Syl

end
