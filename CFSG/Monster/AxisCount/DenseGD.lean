module

public import CFSG.Monster.AxisCount.DenseApplyW
public import CFSG.Monster.AxisCount.DenseApplyX

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.AxisCount

open CFSG.Monster CFSG.Monster.B CFSG.Monster.Code CFSG.Monster.Spin CFSG.Monster.SpinLattice
  CFSG.Monster.ScalarKernel CFSG.Monster.Visible CFSG.Monster.Griess CFSG.Monster.B.Rep4371 Matrix

theorem applyGD_sound
    (g : Native.GD) (P : Pvis) (hg : GDSpec g P) (v : Native.DVec) :
    interp (Native.applyGD (Native.mkCtx ()) g v) = thetaEquiv P (interp v) := by
  rw [thetaEquiv_apply, theta_apply]
  exact Prod.ext (interpA_applyGD g P hg v)
    (Prod.ext (interpX_applyGD g P hg v) (interpW_applyGD g P hg v))

theorem tabT_get (f : Model.Pauli → Model.Pauli) (a : ℕ) (ha : a < 4096) :
    (Native.tabT f)[a]! = f (false, a, 0) := by
  unfold Native.tabT
  rw [Array.getElem!_eq_getD, Array.getD_eq_getD_getElem?, Array.getElem?_map, Array.getElem?_range]
  simp [ha]

theorem tabD_get (f : Model.Pauli → Model.Pauli) (d : ℕ) (hd : d < 4096) :
    (Native.tabD f)[d]! = f (false, 0, d) := by
  unfold Native.tabD
  rw [Array.getElem!_eq_getD, Array.getD_eq_getD_getElem?, Array.getElem?_map, Array.getElem?_range]
  simp [hd]

theorem pairN_zero_right (x : ℕ) : Model.pairN x 0 = false := by
  unfold Model.pairN Model.parN
  rw [Nat.and_zero]
  decide

theorem pauli_decomp (s : Bool) (a d : ℕ) :
    Model.Pauli.mul (s, 0, 0) (Model.Pauli.mul (false, a, 0) (false, 0, d)) = (s, a, d) := by
  simp [Model.Pauli.mul, pairN_zero_right]

theorem conjQ_pauliQ_central (P : Pvis) (s : Bool) :
    conjQ P (pauliQ (s, 0, 0)) = pauliQ (s, 0, 0) := by
  have h : pauliQ (s, 0, 0) = zQ ^ (boolZ s).val := by
    rw [zQ_pow_val, pauliQ]
    exact congrArg spinEquiv (SpinCoord.ext rfl toC_zero toD_zero)
  rw [h, map_pow, conjQ_zQ]

theorem fastAct_conj (P : Pvis) (f : Model.Pauli → Model.Pauli)
    (hf : ∀ y, conjQ P (pauliQ y) = pauliQ (f y)) (y : Model.Pauli) :
    conjQ P (pauliQ y) = pauliQ (Native.fastAct (Native.tabT f) (Native.tabD f) y) := by
  obtain ⟨s, a, d⟩ := y
  have hmodA : pauliQ (false, a % 4096, 0) = pauliQ (false, a, 0) := by
    simp only [pauliQ, toSC, pauli_s, pauli_a, pauli_d, toC_mod_4096]
  have hmodD : pauliQ (false, 0, d % 4096) = pauliQ (false, 0, d) := by
    simp only [pauliQ, toSC, pauli_s, pauli_a, pauli_d, toD_mod_4096]
  have hA : pauliQ (f (false, a % 4096, 0)) = pauliQ (f (false, a, 0)) :=
    ((hf (false, a % 4096, 0)).symm.trans (congrArg (conjQ P) hmodA)).trans (hf (false, a, 0))
  have hD : pauliQ (f (false, 0, d % 4096)) = pauliQ (f (false, 0, d)) :=
    ((hf (false, 0, d % 4096)).symm.trans (congrArg (conjQ P) hmodD)).trans (hf (false, 0, d))
  have hT : (Native.tabT f)[a % 4096]! = f (false, a % 4096, 0) :=
    tabT_get f (a % 4096) (Nat.mod_lt _ (by norm_num))
  have hD' : (Native.tabD f)[d % 4096]! = f (false, 0, d % 4096) :=
    tabD_get f (d % 4096) (Nat.mod_lt _ (by norm_num))
  have hfa : Native.fastAct (Native.tabT f) (Native.tabD f) (s, a, d) =
      Model.Pauli.mul (s, 0, 0) (Model.Pauli.mul (f (false, a % 4096, 0)) (f (false, 0, d % 4096))) := by
    unfold Native.fastAct
    simp only [hT, hD', native_Pauli_mul]
  have h1 := pauliQ_mul (false, a, 0) (false, 0, d)
  have h2 := pauliQ_mul (s, 0, 0) (Model.Pauli.mul (false, a, 0) (false, 0, d))
  rw [pauli_decomp] at h2
  have hdecomp : pauliQ (s, a, d) =
      pauliQ (s, 0, 0) * (pauliQ (false, a, 0) * pauliQ (false, 0, d)) :=
    h2.trans (congrArg (pauliQ (s, 0, 0) * ·) h1)
  have e1 := map_mul (conjQ P) (pauliQ (s, 0, 0)) (pauliQ (false, a, 0) * pauliQ (false, 0, d))
  have e2 := map_mul (conjQ P) (pauliQ (false, a, 0)) (pauliQ (false, 0, d))
  have hconj : conjQ P (pauliQ (s, a, d)) =
      pauliQ (s, 0, 0) * (pauliQ (f (false, a, 0)) * pauliQ (f (false, 0, d))) :=
    (congrArg (conjQ P) hdecomp).trans (e1.trans (congrArg₂ (· * ·) (conjQ_pauliQ_central P s)
      (e2.trans (congrArg₂ (· * ·) (hf (false, a, 0)) (hf (false, 0, d))))))
  have h3 := pauliQ_mul (s, 0, 0)
    (Model.Pauli.mul (f (false, a % 4096, 0)) (f (false, 0, d % 4096)))
  have h4 := pauliQ_mul (f (false, a % 4096, 0)) (f (false, 0, d % 4096))
  have hrhs : pauliQ (Native.fastAct (Native.tabT f) (Native.tabD f) (s, a, d)) =
      pauliQ (s, 0, 0) * (pauliQ (f (false, a, 0)) * pauliQ (f (false, 0, d))) :=
    (congrArg pauliQ hfa).trans (h3.trans (congrArg₂ (· * ·) rfl (h4.trans (congrArg₂ (· * ·) hA hD))))
  exact hconj.trans hrhs.symm

end CFSG.Monster.AxisCount
