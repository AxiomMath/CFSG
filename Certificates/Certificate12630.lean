module

public import Mathlib.Algebra.Group.Subgroup.Lattice
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.MaximalityAmbient.Over77Data
import Certificates.Kernel.Over77.Glue
public import Mathlib.Algebra.Group.End

public section

namespace Certificates

open CFSG.AGLEmbeddingD2.Wilson.MaximalityAmbient.Over77 in
theorem certificate12630 : ∀ (pA pB pZ σ : Equiv.Perm (Fin 77)) (s : Fin 9 → Equiv.Perm (Fin 77)),
    Array.ofFn (fun i => (pA i : Nat)) = dataA → Array.ofFn (fun i => (pB i : Nat)) = dataB →
    Array.ofFn (fun i => (pZ i : Nat)) = dataZ → Array.ofFn (fun i => (σ i : Nat)) = dataSigma →
    (∀ k : Fin 9, Array.ofFn (fun i => (s k i : Nat)) = dataS.getD k idA) →
    ∀ L : Subgroup (Equiv.Perm (Fin 77)), Subgroup.closure {pA, pB, pZ} ≤ L →
      L ≤ Subgroup.closure (Set.range s) → ¬ L ≤ Subgroup.closure {pA, pB, pZ} → σ ∈ L := CFSG.KD.Over77.c12630_over77

end Certificates
