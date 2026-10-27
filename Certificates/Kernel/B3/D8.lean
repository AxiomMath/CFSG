module

public import Certificates.Data.Kernel.B3Mask
import CFSG.Certificates.Kernel.Common.JsonGz
import CFSG.Certificates.Kernel.Common.Repo

public section

#kc_repo #kc_json_gz CFSG.KD.B3M8 "Certificates/Kernel/B3/data/n8.json.gz"
  128354 7000828438839842735
  (n : Nat) (nT : Nat) (e : Nat) (m : Nat) (iw : Nat) (TN : Nat) (mtN : Nat) (CN : Nat) (DN : Nat)
  (Db : List (List Nat)) (nD : Nat) (ext : List (List (Nat × Nat))) (WN : Nat) (FN : Nat)
  (Am : List (List Nat)) (A0 : List Nat) (nmw : List Nat) (dtw : List (Nat × Nat)) (S5 : List Nat)
  (ch5 : List (Nat × Nat × Nat)) (FV : List (List Nat)) (JU : List Nat) (JS : List (List Nat))
  (Jch : List (List (Nat × Nat × Nat))) (cov : List (List (List Nat)))

namespace CFSG.KD.B3M8

@[expose] noncomputable def dat : CFSG.KC.B3M.Dat :=
  ⟨n, nT, e, m, iw, TN, mtN, CN, DN, Db, nD, ext, WN, FN, Am, A0, nmw, dtw, S5, ch5, FV, JU, JS,
    Jch, cov⟩

end CFSG.KD.B3M8

end
