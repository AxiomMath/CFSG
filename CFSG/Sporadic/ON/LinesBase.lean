
module

public import Certificates.Data.CFSGNative.ON.Certificate
public import CFSG.Sporadic.ON.VecSpec

@[expose] public section

namespace CFSG.Sporadic.ON

open Native Matrix
open CFSG.F3.Native CFSG.Sporadic.Fi23.Native CFSG.Sporadic.Th CFSG.Sporadic.Th.Native
open CFSG.Perm CFSG.Perm.Native

private theorem bitVal_ne_zero : ∀ p m : Bool, (p || m) = true → bitVal p m ≠ 0 := by decide

theorem vecOf_ne_zero {c : W} {t : ℕ} (ht : t < 154) (h : (c.bitP t || c.bitM t) = true) :
    vecOf c ⟨t, ht⟩ ≠ 0 := by
  rw [vecOf_apply, V.val_eq_bitVal, ← W.bitP_eq, ← W.bitM_eq]
  exact bitVal_ne_zero _ _ h

noncomputable abbrev line0 : Fin nLines := ⟨0, by norm_num⟩

end CFSG.Sporadic.ON
