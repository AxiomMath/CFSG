module

public import Certificates.Data.M23Pair
import all Certificates.Data.M23Pair
import all CFSG.Fischer.F4

public section

open CFSG.M23Pair CFSG.Fischer CFSG.Monster.B.Classical.Plane
open CFSG.QuasithinUnique.Vol2Native.L239
open scoped Matrix

namespace Certificates

set_option maxHeartbeats 0 in
open CFSG.M23Pair CFSG.Fischer CFSG.Monster.B.Classical.Plane in
open CFSG.QuasithinUnique.Vol2Native.L239 in
open scoped Matrix in
theorem certificate7107 :
    (∀ a : Fin 21, hepL a ∈ M23Insp.data.H) ∧
    heptThrough.length = 21 ∧
    (((sbar : ↥CFSG.Blueprint.NativeSporadic.M23) : Equiv.Perm (Fin 23)) 21 = 22 ∧
      ((sbar : ↥CFSG.Blueprint.NativeSporadic.M23) : Equiv.Perm (Fin 23)) 22 = 21) ∧
    (∀ i : Fin 21, lamInv (((sbar : ↥CFSG.Blueprint.NativeSporadic.M23) :
      Equiv.Perm (Fin 23)) (lam i)) = normIdx (A0 *ᵥ frobVec (Ω i))) ∧
    (∀ k : Fin 16, ∀ i : Fin 21, lamInv (((M23Insp.es.getD k 1 :
      ↥CFSG.Blueprint.NativeSporadic.M23) : Equiv.Perm (Fin 23)) (lam i)) =
        normIdx (waxM (uCo k) *ᵥ Ω i)) :=
  ⟨by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel⟩,
    by decide +kernel, by decide +kernel⟩

end Certificates
