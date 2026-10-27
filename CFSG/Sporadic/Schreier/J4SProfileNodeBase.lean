
module

public import CFSG.Sporadic.Schreier.J4SProfileCheckBase
public import CFSG.Sporadic.Schreier.J4SNative
public import CFSG.Sporadic.Schreier.J4SCols
public import CFSG.Sporadic.Schreier.J4SOrbitsBase
public meta import CFSG.Sporadic.Schreier.J4SOrbitsBase
public import CFSG.Sporadic.Schreier.J4SProfile
public meta import CFSG.Sporadic.Schreier.J4SProfile
public import CFSG.Sporadic.Schreier.J4SSylowData
public meta import CFSG.Sporadic.Schreier.J4SSylowData
public import CFSG.Sporadic.J4.Local
public import CFSG.Sporadic.Schreier.J4SSylowBase1
public import CFSG.Sporadic.J4.QT2LocCntProofBase
public import CFSG.Sporadic.J4.QT2LocZProof
public import CFSG.Sporadic.J4.QTOutChar

@[expose] public noncomputable section

namespace CFSG.Sporadic.J4Schreier

open CFSG.Sporadic.J4 CFSG.Sporadic.GLQ CFSG.Sporadic.SmallF2 CFSG.Sporadic.SmallF2.Native
open scoped Matrix

theorem kfun_spec (n e : ℕ) (h : kfun n e < 5) :
    stepNF^[kfun n e] (n, e) = (0, 0) ∧ ∀ m < kfun n e, stepNF^[m] (n, e) ≠ (0, 0) := by
  unfold kfun at h ⊢
  cases hf : (List.range 5).find? (fun m => stepNF^[m] (n, e) == (0, 0)) with
  | none => rw [hf, Option.getD_none] at h; omega
  | some k =>
    rw [Option.getD_some]
    obtain ⟨hk, i, hi, hik, hmin⟩ := List.find?_eq_some_iff_getElem.1 hf
    rw [List.getElem_range] at hik
    subst hik
    refine ⟨beq_iff_eq.1 hk, fun m hm => ?_⟩
    have := hmin m hm
    rw [List.getElem_range] at this
    intro heq
    rw [heq] at this
    exact absurd this (by decide)

end CFSG.Sporadic.J4Schreier
