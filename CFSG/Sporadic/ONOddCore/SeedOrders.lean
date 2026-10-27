module

public import CFSG.Sporadic.ONOddCore.SeedOrdersCheckInputs
public import CFSG.Sporadic.Schreier.ONVectorOrder

public noncomputable section

namespace CFSG.Sporadic.ONOddCore

open CFSG.ONSchreier CFSG.ONSchreier.Native CFSG.Sporadic.ON CFSG.Sporadic.ON.Native

theorem prep_ppow {x : Array ℕ} {X : Equiv.Perm (Fin N)} (hx : PRep N x X) :
    ∀ k, PRep N (ppow x k) (X ^ k)
  | 0 => by simpa [ppow] using prep_pid (n := N)
  | k + 1 => by
    rw [ppow, pow_succ']
    exact prep_pcomp hx (prep_ppow hx k)

theorem ne_of_peq_false {t u : Array ℕ} {g h : Equiv.Perm (Fin N)} (ht : PRep N t g)
    (hu : PRep N u h) (he : peq nPts t u = false) : g ≠ h := fun hgh => by
  have := (peq_iff ht hu).2 hgh
  rw [he] at this
  exact Bool.false_ne_true this

theorem seed_facts :
    PRep N (natTab (vorbit (digitsW Data.rootDigits)).alpha) a0 ∧
      PRep N (natTab (vorbit (digitsW Data.rootDigits)).beta) a1 := by
  rw [← vectorOrbit_def]
  exact ⟨prep_a0, prep_a1⟩

end CFSG.Sporadic.ONOddCore
