module

import CFSG.Certificates.Kernel.Common.JsonGz
import CFSG.Certificates.Kernel.Common.Repo
public import Certificates.Data.Kernel.Co2Census.Spin

public section

#kc_repo #kc_json_gz CertificateChecks.KernelCo2Census.SpJ
  "Certificates/Kernel/Co2Census/data/spin.json.gz" 59601 9084159440546502203
  (LSP : List (List (List Nat))) (ASP : List (List Nat)) (BSP : List (List Nat))
  (GSP : List (List (List Nat))) (GOFF : List Nat) (TSP : List (List (List Nat)))

namespace CertificateChecks.KernelCo2Census

open CFSG.KC.Co2Census

@[expose] noncomputable def lspF (k : Nat) : List (List Nat) := SpJ.LSP.getD k []

@[expose] noncomputable def abF (x : Nat) : List (List Nat) := if x = 2 then SpJ.ASP else SpJ.BSP

@[expose] noncomputable def gspF (k l : Nat) : List (List Nat) :=
  SpJ.GSP.getD (SpJ.GOFF.getD k 0 + l) []

@[expose] noncomputable def tspF (i : Nat) : List (List Nat) := SpJ.TSP.getD i []

@[expose] noncomputable def spinMV (n : Nat) (v : List Nat) : List Nat :=
  mvRP (tspF (n % 63)) (mvRP (tspF (63 + n / 63 % 32)) (mvRP (tspF (95 + n / 2016 % 15))
    (mvRP (tspF (110 + n / 30240 % 8)) (mvRP (tspF (118 + n / 241920 % 3))
      (mvRP (tspF (121 + n / 725760 % 2)) v)))))

end CertificateChecks.KernelCo2Census

end
