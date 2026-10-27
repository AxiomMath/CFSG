module

public import CFSG.Quasithin.Vol2.Ch4Sec2NSBKTens

public section

namespace CFSG.Quasithin.H13.Ch4.NSB

open Matrix

@[expose] def actM {j n : ℕ} (B : Matrix (Fin n) (Fin n) (ZMod 2)) (Y : Fin j → Fin n → ZMod 2) :
    Fin j → Fin n → ZMod 2 :=
  fun i => B.mulVec (Y i)

theorem actM_apply {j n : ℕ} (B : Matrix (Fin n) (Fin n) (ZMod 2)) (Y : Fin j → Fin n → ZMod 2)
    (i : Fin j) : actM B Y i = B.mulVec (Y i) := rfl

theorem actM_add {j n : ℕ} (B : Matrix (Fin n) (Fin n) (ZMod 2)) (Y Y' : Fin j → Fin n → ZMod 2) :
    actM B (Y + Y') = actM B Y + actM B Y' := by
  funext i
  simp [actM, Matrix.mulVec_add]

theorem actM_add_left {j n : ℕ} (B B' : Matrix (Fin n) (Fin n) (ZMod 2))
    (Y : Fin j → Fin n → ZMod 2) : actM (B + B') Y = actM B Y + actM B' Y := by
  funext i
  simp [actM, Matrix.add_mulVec]

theorem actM_mul {j n : ℕ} (B B' : Matrix (Fin n) (Fin n) (ZMod 2)) (Y : Fin j → Fin n → ZMod 2) :
    actM (B * B') Y = actM B (actM B' Y) := by
  funext i
  simp [actM, Matrix.mulVec_mulVec]

theorem actM_one {j n : ℕ} (Y : Fin j → Fin n → ZMod 2) : actM 1 Y = Y := by
  funext i
  simp [actM]

theorem actM_tens {j n : ℕ} (B : Matrix (Fin n) (Fin n) (ZMod 2)) (a : Fin n → ZMod 2)
    (x : Fin j → ZMod 2) : actM B (tens a x) = tens (B.mulVec a) x :=
  tens_mulVec B a x

theorem tm_neg_eq_self {j n : ℕ} (Y : Fin j → Fin n → ZMod 2) : -Y = Y := by
  funext i b
  simp only [Pi.neg_apply]
  have h : ∀ c : ZMod 2, -c = c := by decide
  exact h _

theorem tm_add_self {j n : ℕ} (Y : Fin j → Fin n → ZMod 2) : Y + Y = 0 := by
  funext i b
  simp only [Pi.add_apply, Pi.zero_apply]
  have h : ∀ c : ZMod 2, c + c = 0 := by decide
  exact h _

end CFSG.Quasithin.H13.Ch4.NSB
