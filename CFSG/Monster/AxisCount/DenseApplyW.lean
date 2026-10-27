module

public import CFSG.Monster.AxisCount.DenseApply

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.AxisCount

open CFSG.Monster CFSG.Monster.B CFSG.Monster.Code CFSG.Monster.Spin CFSG.Monster.SpinLattice
  CFSG.Monster.ScalarKernel CFSG.Monster.Visible CFSG.Monster.Griess CFSG.Monster.B.Rep4371 Matrix

theorem sum_range_mul24 {M : Type*} [AddCommMonoid M] (f : ℕ → M) (r : ℕ) :
    ∑ k ∈ Finset.range (r * 24), f k =
      ∑ a ∈ Finset.range r, ∑ j ∈ Finset.range 24, f (a * 24 + j) := by
  induction r with
  | zero => simp
  | succ r ih =>
    have h1 : ∑ k ∈ Finset.range ((r + 1) * 24), f k =
        ∑ k ∈ Finset.range (r * 24), f k + ∑ j ∈ Finset.range 24, f (r * 24 + j) := by
      rw [show (r + 1) * 24 = r * 24 + 24 by ring]
      exact Finset.sum_range_add f (r * 24) 24
    rw [h1, ih, Finset.sum_range_succ (fun a => ∑ j ∈ Finset.range 24, f (a * 24 + j)) r]

@[expose] def rowCoef (L : List (ℕ × ℤ)) (rs : ℕ) : ℤ := (L.map fun t => if t.1 = rs then t.2 else 0).sum

theorem list_sum_cols (L : List (ℕ × ℤ)) (rs j' : ℕ) (hj : j' < 24) (c : ℕ → ℤ) :
    ∑ j ∈ Finset.range 24, ((L.map fun t => (t.1 * 24 + j, t.2)).map fun t' =>
        if t'.1 = rs * 24 + j' then t'.2 * c j else 0).sum = rowCoef L rs * c j' := by
  induction L with
  | nil => simp [rowCoef]
  | cons t L ih =>
    simp only [List.map_cons, List.sum_cons, Finset.sum_add_distrib, ih, rowCoef, add_mul] at ih ⊢
    congr 1
    rw [Finset.sum_eq_single j']
    · by_cases ht : t.1 = rs
      · simp [ht]
      · have : t.1 * 24 + j' ≠ rs * 24 + j' := fun e => ht (by omega)
        simp [ht]
    · intro j hjm hjj
      have hj'' := Finset.mem_range.1 hjm
      have : t.1 * 24 + j ≠ rs * 24 + j' := fun e => hjj (by omega)
      simp [this]
    · intro h
      exact absurd (Finset.mem_range.2 hj) h

theorem wScatter_getD (g : Native.GD) (W1 : Array ℤ) (rs j' : ℕ) (hrs : rs < 4096) (hj : j' < 24) :
    (Native.scatterAt 0 98304 g.wT W1).getD (rs * 24 + j') 0 =
      ∑ r ∈ Finset.range 4096, rowCoef (g.rowT[r]!) rs * W1.getD (r * 24 + j') 0 := by
  have hq : rs * 24 + j' < 98304 := by omega
  rw [Native.scatterAt_getD _ _ _ _ _ hq, show (98304 : ℕ) = 4096 * 24 from rfl,
    sum_range_mul24]
  refine Finset.sum_congr rfl fun r _ => ?_
  have h := list_sum_cols (g.rowT[r]!) rs j' hj (fun j => W1.getD (r * 24 + j) 0)
  rw [← h]
  refine Finset.sum_congr rfl fun j hjr => ?_
  have hj' : j < 24 := Finset.mem_range.1 hjr
  have e1 : (r * 24 + j) / 24 = r := by omega
  have e2 : (r * 24 + j) % 24 = j := by omega
  simp only [Native.GD.wT, e1, e2, zero_add]

theorem cast_rowCoef (L : List (ℕ × ℤ)) (rs : ℕ) :
    ((rowCoef L rs : ℤ) : ℚ) = (L.map fun t => if t.1 = rs then (t.2 : ℚ) else 0).sum := by
  induction L with
  | nil => simp [rowCoef]
  | cons t L ih =>
    simp only [rowCoef, List.map_cons, List.sum_cons, Int.cast_add] at ih ⊢
    rw [ih]
    split_ifs <;> simp

theorem spin_entry (P : Pvis) (g : Native.GD) (hg : GDSpec g P) (s s' : SpinIdx) :
    (P.1.1 : Matrix SpinIdx SpinIdx ℚ) s s' =
      ((g.rowT[rowOf s]!).map fun t =>
        ((t.2 : ℚ) / 2 ^ g.rowS) * (if t.1 = rowOf s' then 1 else 0)).sum := by
  have h := hg.row (rowOf s) (rowOf_lt s)
  rw [spinOfRow_rowOf] at h
  have h2 := congrFun h s'
  have h3 : ((Pi.single s (1 : ℚ) : SpinIdx → ℚ) ᵥ* (P.1.1 : Matrix SpinIdx SpinIdx ℚ)) s' =
      (P.1.1 : Matrix SpinIdx SpinIdx ℚ) s s' := by
    simp [Matrix.vecMul, dotProduct, Pi.single_apply]
  rw [h3] at h2
  rw [h2]
  have hrs := rowOf_lt s'
  generalize g.rowT[rowOf s]! = L
  induction L with
  | nil => simp
  | cons t L ih =>
    simp only [List.map_cons, List.sum_cons, Pi.add_apply, Pi.smul_apply, smul_eq_mul, eRow_apply]
    rw [ih]
    congr 1
    by_cases ht : t.1 = rowOf s'
    · simp [ht, hrs]
    · simp [ht]


theorem rowSum_div (L : List (ℕ × ℤ)) (rs : ℕ) (d : ℚ) :
    (L.map fun t => ((t.2 : ℚ) / d) * (if t.1 = rs then 1 else 0)).sum = (rowCoef L rs : ℚ) / d := by
  rw [cast_rowCoef]
  induction L with
  | nil => simp
  | cons t L ih =>
    simp only [List.map_cons, List.sum_cons, add_div]
    rw [ih]
    split_ifs <;> simp

theorem sum_spin (F : SpinIdx → ℚ) :
    ∑ l : SpinIdx, F l = ∑ r ∈ Finset.range 4096, F (spinOfRow r) := by
  rw [← Equiv.sum_comp spinRowEquiv, Finset.sum_range (fun r => F (spinOfRow r))]
  rfl

theorem wMul_cast (G D : Array ℤ) (r j : ℕ) (hr : r < 4096) (hj : j < 24) :
    (((Native.wMul G D).getD (r * 24 + j) 0 : ℤ) : ℚ) =
      ∑ k : Fin 24, ((D.getD (98580 + r * 24 + k) 0 : ℤ) : ℚ) * ((G.getD (k * 24 + j) 0 : ℤ) : ℚ) := by
  rw [Native.wMul_getD _ _ _ _ hr hj, Int.cast_sum, Finset.sum_range]
  refine Finset.sum_congr rfl fun k _ => ?_
  push_cast
  rfl

theorem interpW_applyGD (g : Native.GD) (P : Pvis) (hg : GDSpec g P) (v : Native.DVec) :
    interpW (Native.applyGD (Native.mkCtx ()) g v) =
      thetaW (P.1.1 : Matrix SpinIdx SpinIdx ℚ) (mat P.1.2) (interpW v) := by
  ext s' j'
  have hrs := rowOf_lt s'
  have hj := j'.2
  have hk1 : ¬ 98580 + 24 * rowOf s' + (j' : ℕ) < 300 := by omega
  have hk2 : ¬ 98580 + 24 * rowOf s' + (j' : ℕ) < 98580 := by omega
  have hidx : 98580 + 24 * rowOf s' + (j' : ℕ) - 98580 = rowOf s' * 24 + j' := by omega
  have hL : (Native.applyGD (Native.mkCtx ()) g v).D.getD (98580 + 24 * rowOf s' + j') 0 =
      (∑ r ∈ Finset.range 4096, rowCoef (g.rowT[r]!) (rowOf s') *
        (Native.wMul g.G v.D).getD (r * 24 + j') 0) * 2 ^ (g.eNew - g.latS - g.rowS) := by
    rw [Native.applyGD_getD, ite_eq_right hk1, ite_eq_right hk2, hidx,
      wScatter_getD g _ _ _ hrs hj]
  have step1 : ∀ (S : Matrix SpinIdx SpinIdx ℚ) (N : Matrix SpinIdx (Fin 24) ℚ)
      (G : Matrix (Fin 24) (Fin 24) ℚ) (s' : SpinIdx) (j' : Fin 24),
      (Sᵀ * N * G) s' j' = ∑ l : SpinIdx, S l s' * ∑ k : Fin 24, N l k * G k j' := by
    intro S N G s' j'
    rw [Matrix.mul_assoc]
    simp only [Matrix.mul_apply, transpose_apply]
  have hterm : ∀ r ∈ Finset.range 4096,
      (P.1.1 : Matrix SpinIdx SpinIdx ℚ) (spinOfRow r) s' *
        ∑ k : Fin 24, interpW v (spinOfRow r) k * mat P.1.2 k j' =
      (rowCoef (g.rowT[r]!) (rowOf s') : ℚ) *
        (((Native.wMul g.G v.D).getD (r * 24 + j') 0 : ℤ) : ℚ) /
          2 ^ (g.rowS + (v.e + g.latS)) := by
    intro r hr
    have hr' : r < 4096 := Finset.mem_range.1 hr
    rw [spin_entry P g hg, rowOf_spinOfRow hr', rowSum_div, wMul_cast _ _ _ _ hr' hj]
    simp only [interpW, of_apply, rowOf_spinOfRow hr', hg.lat]
    rw [Finset.mul_sum, Finset.mul_sum, Finset.sum_div]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [show 24 * r = r * 24 from mul_comm _ _, pow_add, pow_add]
    field_simp
  show ((((Native.applyGD (Native.mkCtx ()) g v).D.getD (98580 + 24 * rowOf s' + j') 0 : ℤ) : ℚ)) /
    2 ^ (Native.applyGD (Native.mkCtx ()) g v).e = _
  rw [thetaW_apply, step1, sum_spin, Finset.sum_congr rfl hterm, hL, Native.applyGD_e]
  have hge := (eNew_ge g)
  have h2 : (2 : ℚ) ^ (v.e + g.eNew) =
      2 ^ (g.rowS + (v.e + g.latS)) * 2 ^ (g.eNew - g.latS - g.rowS) := by
    rw [← pow_add, show v.e + g.eNew = g.rowS + (v.e + g.latS) + (g.eNew - g.latS - g.rowS) by omega]
  push_cast
  rw [h2, Finset.sum_mul, Finset.sum_div]
  refine Finset.sum_congr rfl fun r _ => ?_
  field_simp

end CFSG.Monster.AxisCount
