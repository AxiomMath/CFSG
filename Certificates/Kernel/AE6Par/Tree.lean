module

public import Certificates.Data.Kernel.AE6Par.Defs

public section

set_option maxRecDepth 100000

namespace CertificateChecks.KernelAE6Par

open Equiv Certificates.AE6Par Certificates.AE6Par.K

theorem ae6par_tree : treeElt 0 = 1 ∧ treeP.length = 191 ∧ ∀ i ∈ List.range 191,
    (treeP.getD i (0, 0)).2 ≤ i ∧ (treeP.getD i (0, 0)).1 < gens.length ∧
    treeElt (i + 1) = genElt (treeP.getD i (0, 0)).1 * treeElt (treeP.getD i (0, 0)).2 := by
  decide +kernel

theorem ae6par_keys : (List.range 192).map (fun i => permKey (treeElt i)) = treeKeys := by
  decide +kernel

theorem ae6par_keys_nodup : treeKeys.Nodup := by
  decide +kernel

end CertificateChecks.KernelAE6Par
