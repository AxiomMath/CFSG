module

public import Certificates.Data.M23Heptad

public section

open Equiv CFSG.M23Heptad CFSG.A7Fano CFSG.QuasithinUnique.Vol2Native.L239

namespace Certificates

set_option maxHeartbeats 0 in
open Equiv CFSG.M23Heptad CFSG.A7Fano CFSG.QuasithinUnique.Vol2Native.L239 in
theorem certificate7098 :
    (∀ i : Fin 7, ((liftCyc : ↥CFSG.Blueprint.NativeSporadic.M23) : Perm (Fin 23)) (ιbar i) =
      ιbar (cyc7 i)) ∧
    (∀ i : Fin 7, ((liftDbl : ↥CFSG.Blueprint.NativeSporadic.M23) : Perm (Fin 23)) (ιbar i) =
      ιbar (dbl7 i)) ∧
    (∀ i : Fin 7, ((liftG1 : ↥CFSG.Blueprint.NativeSporadic.M23) : Perm (Fin 23)) (ιbar i) =
      ιbar (g1perm i)) ∧
    liftCyc * ubar0 * liftCyc⁻¹ = ubar0 ∧ liftDbl * ubar0 * liftDbl⁻¹ = ubar0 ∧
    liftG1 * ubar0 * liftG1⁻¹ = ubar0 ∧ ubar0 ≠ 1 ∧
    (∀ i : Fin 16, M23Insp.es.getD i 1 ≠ 1 →
      conjElt i * ubar0 * (conjElt i)⁻¹ = M23Insp.es.getD i 1) ∧
    (∀ i : Fin 16, ((M23Insp.es.getD i 1 : ↥CFSG.Blueprint.NativeSporadic.M23) :
      Perm (Fin 23)) 0 = 0 → M23Insp.es.getD i 1 = 1) ∧
    (M23Insp.es.map fun e => ((e : ↥CFSG.Blueprint.NativeSporadic.M23) : Perm (Fin 23)) 0).Nodup := by decide +kernel

end Certificates
