module

public import CFSG.Monster.AxisCount.DenseInterp

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.AxisCount

open CFSG.Monster CFSG.Monster.B CFSG.Monster.Code CFSG.Monster.Spin CFSG.Monster.SpinLattice
  CFSG.Monster.ScalarKernel CFSG.Monster.Visible CFSG.Monster.Griess CFSG.Monster.B.Rep4371 Matrix

structure GDSpec (g : Native.GD) (P : Pvis) : Prop where
  lat : ∀ i j : Fin 24, mat P.1.2 i j = ((g.G.getD (i * 24 + j) 0 : ℤ) : ℚ) / 2 ^ g.latS
  conj : ∀ y : Model.Pauli, conjQ P (pauliQ y) = pauliQ (Native.fastAct g.tT g.tD y)
  row : ∀ r, r < 4096 →
    (Pi.single (spinOfRow r) (1 : ℚ) : SpinIdx → ℚ) ᵥ* (P.1.1 : Matrix SpinIdx SpinIdx ℚ) =
      ((g.rowT[r]!).map fun t => ((t.2 : ℚ) / 2 ^ g.rowS) • eRow t.1).sum

theorem pow_two_sub (a b : ℕ) (h : a ≤ b) : (2 : ℚ) ^ (b - a) * 2 ^ a = 2 ^ b := by
  rw [← pow_add, Nat.sub_add_cancel h]

theorem eNew_ge (g : Native.GD) : 2 * g.latS ≤ g.eNew ∧ g.latS + g.rowS ≤ g.eNew :=
  ⟨le_max_left _ _, le_max_right _ _⟩

theorem sum_fin24 {M : Type*} [AddCommMonoid M] (f : ℕ → M) :
    ∑ i : Fin 24, f i = ∑ i ∈ Finset.range 24, f i :=
  (Finset.sum_range f).symm

theorem interpA_applyGD
    (g : Native.GD) (P : Pvis) (hg : GDSpec g P) (v : Native.DVec) :
    interpA (Native.applyGD (Native.mkCtx ()) g v) = thetaA (mat P.1.2) (interpA v) := by
  apply Subtype.ext
  ext i j
  have hi := i.2
  have hj := j.2
  have hidx := (Native.aIdx_spec i j hi hj).1
  have h1 : (Native.applyGD (Native.mkCtx ()) g v).D.getD (Native.aIdx i j) 0 =
      (Native.latA g.G v.D).getD (Native.aIdx i j) 0 * 2 ^ (g.eNew - 2 * g.latS) := by
    rw [Native.applyGD_getD, ite_eq_left hidx]
  have hsum : (Native.latA g.G v.D).getD (Native.aIdx i j) 0 =
      ∑ k : Fin 24, ∑ l : Fin 24, g.G.getD (k * 24 + i) 0 * v.D.getD (Native.aIdx k l) 0 *
        g.G.getD (l * 24 + j) 0 := by
    rw [Native.latA_aIdx _ _ _ _ hi hj, Finset.sum_range]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Finset.sum_range]
  rw [coe_thetaA]
  simp only [interpA, of_apply, Matrix.mul_apply, transpose_apply, hg.lat, Submodule.coe_mk]
  rw [h1, hsum, Native.applyGD_e]
  have hge := (eNew_ge g).1
  have h2 : (2 : ℚ) ^ (v.e + g.eNew) = 2 ^ v.e * 2 ^ (2 * g.latS) * 2 ^ (g.eNew - 2 * g.latS) := by
    rw [← pow_add, ← pow_add, show v.e + g.eNew = v.e + 2 * g.latS + (g.eNew - 2 * g.latS) by omega]
  have h3 : (2 : ℚ) ^ (2 * g.latS) = 2 ^ g.latS * 2 ^ g.latS := by
    rw [two_mul, pow_add]
  push_cast
  simp only [Finset.sum_mul, Finset.sum_div]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
  rw [h2, h3]
  field_simp

end CFSG.Monster.AxisCount
