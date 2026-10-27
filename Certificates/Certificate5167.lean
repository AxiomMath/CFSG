module

public import Certificates.Data.L34DC
import CFSG.Certificates.Kernel.L34DCShapeSound
import Certificates.Kernel.L34DC.Checks

public section

namespace Certificates

open Certificates.L34DC

open Certificates.L34DC in
theorem certificate5167 : (∀ i : Fin 192, evalW (word (wordArr ()) i) (gStd ()) = elt i) ∧
    ∀ φ : Elt → Elt, (∀ x y, φ (mulE x y) = mulE (φ x) (φ y)) → Function.Injective φ →
      (∀ x : Elt, x.1 = 0 → x.2.2.2 = 0 → (φ x).1 = 0 ∧ (φ x).2.2.2 = 0) →
      (φ (elt 16)).2.1 = 0 ∧ (φ (elt 16)).2.2.2 = 0 ∧ (φ (elt 16)).1 ≠ 0 ∧
        (φ (elt 4)).1 = 0 ∧ (φ (elt 4)).2.2.2 = 0 ∧ (φ (elt 4)).2.1 ≠ 0 :=
  ⟨fun i => by
      have h := L34DC.wordsOK5167_ok
      unfold wordsOK at h
      exact beq_iff_eq.mp (List.all_eq_true.mp h i (List.mem_finRange i)),
    fun φ hm hi hV => shape_of_checkShape5167 L34DC.checkShape5167_ok φ hm hi hV⟩

end Certificates
