module

public import CFSG.Quasithin.H13.GoldschmidtA6RowsA8Mod
public import CFSG.Quasithin.H13.GoldschmidtA6RowsFast

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

open Matrix

namespace CFSG.Quasithin.H13.A6.GR

namespace Row8

@[expose] def wt (x : Fin 8 → ZMod 2) : ℕ := ∑ i, (x i).val

@[expose] def qf (y : Fin 6 → ZMod 2) : ZMod 2 := ((wt (secM *ᵥ y) / 2 : ℕ) : ZMod 2)

@[expose] def MemQ (K : Matrix (Fin 6) (Fin 6) (ZMod 2)) : Prop := ∀ y, qf (K *ᵥ y) = qf y

theorem wt_pm (σ : Equiv.Perm (Fin 8)) (x : Fin 8 → ZMod 2) : wt (pm σ *ᵥ x) = wt x := by
  unfold wt
  rw [pm_mulVec]
  exact Equiv.sum_comp σ⁻¹ (fun i => (x i).val)

theorem wt_one_add : ∀ x : Fin 8 → ZMod 2, ∑ i, x i = 0 →
    ((wt (x + fun _ => 1) / 2 : ℕ) : ZMod 2) = ((wt x / 2 : ℕ) : ZMod 2) := by decide +kernel

theorem qf_mat8 (σ : Equiv.Perm (Fin 8)) (y : Fin 6 → ZMod 2) : qf (mat8 σ *ᵥ y) = qf y := by
  have hy : ∑ i, (secM *ᵥ y) i = 0 := sec_even y
  have hx0 : ∑ i, (pm σ *ᵥ (secM *ᵥ y)) i = 0 := by rw [pm_sum]; exact hy
  have h1 : mat8 σ *ᵥ y = crdM *ᵥ (pm σ *ᵥ (secM *ᵥ y)) := by
    unfold mat8
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
  unfold qf
  rw [h1]
  rcases sec_crd _ hx0 with h | h
  · rw [h, wt_pm]
  · rw [h, wt_one_add _ hx0, wt_pm]

theorem memQ_mat8 (σ : Equiv.Perm (Fin 8)) : MemQ (mat8 σ) := qf_mat8 σ


@[expose] def qtab8 : ℕ := 14539319466979298042

@[expose] def qb (x : ℕ) : Bool := Nat.beq (Nat.land (Nat.shiftRight qtab8 x) 1) 1

theorem qb_cast : ∀ x < 64, qb x = decide (qf (vecN 6 x) = 1) := by decide +kernel

@[expose] def okQ8 (pre : List ℕ) (c : ℕ) : Bool :=
  qb c == qb (2 ^ pre.length) &&
    (List.range pre.length).all fun i => qb (c ^^^ pre.getD i 0) == qb (2 ^ pre.length ^^^ 2 ^ i)

@[expose] def fullQ8 (_ : List ℕ) : Bool := true

theorem hfull8 (K : Matrix (Fin 6) (Fin 6) (ZMod 2)) (_ : MemQ K) :
    fullQ8 (colsOf 6 K) = true := rfl

theorem hok8 (K : Matrix (Fin 6) (Fin 6) (ZMod 2)) (hK : MemQ K) :
    ∀ j < 6, okQ8 ((colsOf 6 K).take j) ((colsOf 6 K).getD j 0) = true := by
  intro j hj
  have hlen : ((colsOf 6 K).take j).length = j := by simp [colsOf_length, hj.le]
  have hcol : ∀ i (hi : i < 6), vecN 6 ((colsOf 6 K).getD i 0) = K *ᵥ vecN 6 (2 ^ i) := by
    intro i hi
    rw [colsOf_getD laws6 K ⟨i, hi⟩, mulVec_vecN_pow K ⟨i, hi⟩]
  have hlt : ∀ i (hi : i < 6), (colsOf 6 K).getD i 0 < 64 := fun i hi =>
    colsOf_getD_lt laws6 K hi
  have hpw : ∀ i (hi : i < 6), 2 ^ i < 64 := fun i hi => by
    have : 2 ^ i < 2 ^ 6 := Nat.pow_lt_pow_right (by norm_num) hi
    simpa using this
  unfold okQ8
  rw [hlen, Bool.and_eq_true]
  constructor
  · rw [beq_iff_eq, qb_cast _ (hlt j hj), qb_cast _ (hpw j hj), hcol j hj, hK]
  · rw [List.all_eq_true]
    intro i hi
    rw [List.mem_range] at hi
    have hi6 : i < 6 := by omega
    have hget : ((colsOf 6 K).take j).getD i 0 = (colsOf 6 K).getD i 0 := by
      rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_take_of_lt hi]
    rw [hget, beq_iff_eq]
    have h1 : (colsOf 6 K).getD j 0 ^^^ (colsOf 6 K).getD i 0 < 64 := by
      have := Nat.xor_lt_two_pow (n := 6) (hlt j hj) (hlt i hi6)
      simpa using this
    have h2 : 2 ^ j ^^^ 2 ^ i < 64 := by
      have := Nat.xor_lt_two_pow (n := 6) (x := 2 ^ j) (y := 2 ^ i) (hpw j hj) (hpw i hi6)
      simpa using this
    rw [qb_cast _ h1, qb_cast _ h2, vecN_xor, vecN_xor, hcol j hj, hcol i hi6,
      ← Matrix.mulVec_add, hK]

end Row8

end CFSG.Quasithin.H13.A6.GR
