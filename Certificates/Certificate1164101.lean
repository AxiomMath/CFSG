module

public import Certificates.Data.FischerMarkedReflection
import Certificates.Kernel.Fi22Marked.Checks
import Certificates.Kernel.Fi22LH.Final
import Certificates.Kernel.Fi22LH.OrbOK
import Certificates.Kernel.Fi22Core.OrbData
import CFSG.Certificates.Kernel.Fi22MarkedSound

public section

namespace Certificates

open CertificateChecks

open CFSG.OddTranspositions.FischerMarked CFSG.Sporadic.Fi22.Native CFSG.Sporadic.Th.Native in
theorem certificate1164101 : ∀ i j : Fin 351,
    ap (cTab (CFSG.Sporadic.Fi22.Native.orbitData ()) (CFSG.Sporadic.Fi22.Native.genTables (CFSG.Sporadic.Fi22.Native.orbitData ()) (-2)) (((lhData ())[0]!)[i.val]!))
      (((lhData ())[0]!)[j.val]!) =
      ((lhData ())[0]!)[(pointIndex (reflectPoint (point i) (point j))).val]! :=
  CFSG.KS.Fi22Marked.marked_conj KernelFi22LH.lhD KernelFi22LH.orbOK KernelFi22LH.lhD_checks
    KernelFi22C.orbitData_eq KernelFi22Marked.points_ok KernelFi22Marked.rows_ok
    KernelFi22Marked.tree_ok

end Certificates
