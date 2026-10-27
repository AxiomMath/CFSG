module

public import CFSG.Quasithin.Vol2.Ch4Sec2NSBTwist

public section

namespace CFSG.Quasithin.H13.Ch4.NSB

open Matrix

private theorem nsbF_zmod_two_cases : ∀ c : ZMod 2, c = 0 ∨ c = 1 := by
  decide

theorem gl_zmod_two_central {n : ℕ} (g : GL (Fin n) (ZMod 2))
    (hg : ∀ h : GL (Fin n) (ZMod 2), g * h = h * g) : g = 1 := by
  have htrans : ∀ t : Matrix.TransvectionStruct (Fin n) (ZMod 2),
      Commute t.toMatrix (g : Matrix (Fin n) (Fin n) (ZMod 2)) := by
    intro t
    have hu : IsUnit (t.toMatrix).det := by
      rw [Matrix.TransvectionStruct.det]
      exact isUnit_one
    have h := congrArg Units.val (hg (Matrix.GeneralLinearGroup.mk'' t.toMatrix hu))
    rw [Units.val_mul, Units.val_mul] at h
    exact h.symm
  obtain ⟨c, hc⟩ := Matrix.mem_range_scalar_of_commute_transvectionStruct htrans
  rcases nsbF_zmod_two_cases c with rfl | rfl
  ·
    rw [map_zero] at hc
    have h1 := Units.mul_inv g
    rw [← hc, zero_mul] at h1
    apply Units.ext
    rw [Units.val_one, ← hc]
    exact h1
  ·
    rw [map_one] at hc
    exact Units.ext (hc.symm.trans Units.val_one.symm)

end CFSG.Quasithin.H13.Ch4.NSB
