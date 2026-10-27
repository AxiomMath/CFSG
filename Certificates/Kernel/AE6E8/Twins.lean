module

public import Certificates.Data.Kernel.AE6E8.Defs
public import Certificates.Kernel.AE6Tri.Data
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000
namespace CertificateChecks.KernelAE6E8

open CFSG.KC.AE6E8 CFSG.KC.AE6Tri CFSG.KD.AE6Tri

@[expose] def e8KW : List (List Nat) :=
  [[2, 4, 2, 0, 2, 6, 2, 4, 2, 0, 2, 6], [0, 2, 4, 0, 2, 0, 6, 2, 0, 2, 4, 2, 6],
    [2, 4, 2, 0, 2, 6, 2, 4, 2, 0, 2, 6, 0, 2, 4, 0, 2, 0, 6, 2, 0, 2, 4, 2, 6]]

@[expose] def e8D : List (List Nat) := [[4, 5, 2, 3, 0, 1, 6, 7], [6, 7, 2, 3, 4, 5, 0, 1]]

@[expose] noncomputable def e8DG : List (List Nat) := e8D.map fun d => d.map (gl RG)

@[expose] def e8CW : List (List Nat) := [[6], [4]]

@[expose] def e8U : List (List (List Nat)) := [[[0, 0, 0], [0, 1], [1]], [[0, 0, 0], [0, 1], [1]]]

theorem kQ8 : q8OK RG (e8KW.getD 0 []) (e8KW.getD 1 []) = true := by quickRfl

theorem kTwin : kcOK RG e8DG e8KW (e8KW.take 2) e8CW e8U = true := by quickRfl

end CertificateChecks.KernelAE6E8

end
