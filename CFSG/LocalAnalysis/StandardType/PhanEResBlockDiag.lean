module

public import CFSG.LocalAnalysis.StandardType.PhanEFlagAct

public section

namespace CFSG.ClassicalInvolution.Phan.PhanE.Flag

open Module CFSG.Monster.B.Geometry CFSG.ClassicalInvolution.Phan.PhanE
open scoped Matrix

variable {K : Type} [Field K] [Finite K] {f : ℕ} [CharP K 2] {n : ℕ} {d : List ℕ}

@[expose] def BlockDiag (d : List ℕ) (A : Matrix (Fin n) (Fin n) K) : Prop :=
  ∀ b, b + 1 < d.length → ∀ i j : Fin n,
    (d.getD b 0 ≤ i.val ∧ i.val < d.getD (b + 1) 0) →
    ¬ (d.getD b 0 ≤ j.val ∧ j.val < d.getD (b + 1) 0) → A i j = 0 ∧ A j i = 0

private theorem plr_getD_mono {d : List ℕ} (hd : IsCut n d) (i : ℕ) :
    ∀ {j : ℕ}, i ≤ j → j ≤ d.length - 1 → d.getD i 0 ≤ d.getD j 0 := by
  have aux : ∀ k j, j = i + k → j ≤ d.length - 1 → d.getD i 0 ≤ d.getD j 0 := by
    intro k; induction k with
    | zero => intro j hj _; rw [hj, Nat.add_zero]
    | succ k ih =>
      intro j hj hjlen
      have hprev : d.getD (i + k) 0 ≤ d.getD j 0 := by
        have hstep : d.getD (i + k) 0 < d.getD (i + k + 1) 0 := hd.strict (i + k) (by omega)
        rw [show j = i + k + 1 from by omega]; exact hstep.le
      exact le_trans (ih (i + k) rfl (by omega)) hprev
  intro j hij hj
  exact aux (j - i) j (by omega) hj

private theorem plr_getD_le {d : List ℕ} (hd : IsCut n d) {i : ℕ} (hi : i < d.length) :
    d.getD i 0 ≤ n := by
  have h := plr_getD_mono hd i (show i ≤ d.length - 1 by omega) le_rfl
  rwa [hd.last] at h

@[expose] def plr_cutBlock (d : List ℕ) (j : ℕ) : ℕ :=
  Nat.findGreatest (fun b => d.getD b 0 ≤ j) (d.length - 1)

theorem plr_cutBlock_le {d : List ℕ} (hd : IsCut n d) (j : ℕ) :
    d.getD (plr_cutBlock d j) 0 ≤ j :=
  Nat.findGreatest_spec (P := fun b => d.getD b 0 ≤ j) (m := 0) (n := d.length - 1)
    (Nat.zero_le _) (by rw [hd.head]; exact Nat.zero_le j)

theorem plr_cutBlock_lt_of_lt {d : List ℕ} (hd : IsCut n d) {j : ℕ} (hj : j < n) :
    plr_cutBlock d j < d.length - 1 := by
  have hle := plr_cutBlock_le hd j
  have hbnd : plr_cutBlock d j ≤ d.length - 1 := Nat.findGreatest_le _
  by_contra h
  rw [show plr_cutBlock d j = d.length - 1 from by omega, hd.last] at hle
  omega

theorem plr_lt_cutBlock_succ {d : List ℕ} (hd : IsCut n d) {j : ℕ} (hj : j < n) :
    j < d.getD (plr_cutBlock d j + 1) 0 := by
  have hb := plr_cutBlock_lt_of_lt hd hj; by_contra h
  exact (Nat.findGreatest_eq_iff (P := fun b => d.getD b 0 ≤ j) (k := d.length - 1)).1 rfl
    |>.2.2 (Nat.lt_succ_self _) (Nat.succ_le_iff.mpr hb) (le_of_not_gt h)

private theorem plr_cutBlock_add_one_le_of_lt {d : List ℕ} (hd : IsCut n d) {k i : ℕ}
    (hi : i < d.length) (hk : k < d.getD i 0) : plr_cutBlock d k + 1 ≤ i := by
  by_contra h
  have h1 : i ≤ plr_cutBlock d k := by omega
  have h2 := plr_getD_mono hd i h1 (Nat.findGreatest_le (P := fun b => d.getD b 0 ≤ k) _)
  have h3 := plr_cutBlock_le hd k
  omega

private def plr_blockProj (n : ℕ) (lo hi : ℕ) : Matrix (Fin n) (Fin n) K :=
  Matrix.diagonal (fun i : Fin n => if lo ≤ i.val ∧ i.val < hi then (1 : K) else 0)

@[expose] def plr_BlockOne (n : ℕ) (lo hi : ℕ) (A : Matrix (Fin n) (Fin n) K) : Prop :=
  ∀ i j : Fin n, (lo ≤ i.val ∧ i.val < hi) → ¬ (lo ≤ j.val ∧ j.val < hi) →
    A i j = 0 ∧ A j i = 0

private theorem plr_blockProj_comm {A : Matrix (Fin n) (Fin n) K} (hA : BlockDiag d A)
    {b : ℕ} (hb : b + 1 < d.length) :
    plr_blockProj n (d.getD b 0) (d.getD (b + 1) 0) * A =
      A * plr_blockProj n (d.getD b 0) (d.getD (b + 1) 0) := by
  ext i j
  rw [plr_blockProj, Matrix.diagonal_mul, Matrix.mul_diagonal]
  by_cases hi : d.getD b 0 ≤ i.val ∧ i.val < d.getD (b + 1) 0
  · by_cases hj : d.getD b 0 ≤ j.val ∧ j.val < d.getD (b + 1) 0
    · rw [if_pos hi, if_pos hj]; ring
    · rw [if_pos hi, if_neg hj, (hA b hb i j hi hj).1]; ring
  · by_cases hj : d.getD b 0 ≤ j.val ∧ j.val < d.getD (b + 1) 0
    · rw [if_neg hi, if_pos hj, (hA b hb j i hj hi).2]; ring
    · rw [if_neg hi, if_neg hj]; ring

private theorem plr_blockProj_comm_inv {A B : Matrix (Fin n) (Fin n) K}
    (hAB : A * B = 1) (hBA : B * A = 1) {b : ℕ} (hb : b + 1 < d.length)
    (hcomm : plr_blockProj n (d.getD b 0) (d.getD (b + 1) 0) * A =
      A * plr_blockProj n (d.getD b 0) (d.getD (b + 1) 0)) :
    plr_blockProj n (d.getD b 0) (d.getD (b + 1) 0) * B =
      B * plr_blockProj n (d.getD b 0) (d.getD (b + 1) 0) := by
  calc plr_blockProj n (d.getD b 0) (d.getD (b + 1) 0) * B
      = (B * A) * plr_blockProj n (d.getD b 0) (d.getD (b + 1) 0) * B := by
        rw [hBA, one_mul]
    _ = B * (A * plr_blockProj n (d.getD b 0) (d.getD (b + 1) 0)) * B := by
        rw [Matrix.mul_assoc B A]
    _ = B * (plr_blockProj n (d.getD b 0) (d.getD (b + 1) 0) * A) * B := by
        rw [hcomm]
    _ = B * plr_blockProj n (d.getD b 0) (d.getD (b + 1) 0) := by
        rw [← Matrix.mul_assoc B (plr_blockProj n (d.getD b 0) (d.getD (b + 1) 0)) A,
          Matrix.mul_assoc (B * plr_blockProj n (d.getD b 0) (d.getD (b + 1) 0)) A B,
          hAB, mul_one]

theorem BlockDiag.one : BlockDiag d (1 : Matrix (Fin n) (Fin n) K) := by
  intro b hb i j hi hj
  constructor
  · exact Matrix.one_apply_ne (fun h => hj (h ▸ hi))
  · exact Matrix.one_apply_ne (fun h => hj (h.symm ▸ hi))

theorem BlockDiag.mul {A B : Matrix (Fin n) (Fin n) K} (hA : BlockDiag d A) (hB : BlockDiag d B) :
    BlockDiag d (A * B) := by
  intro b hb i j hi hj
  constructor
  · rw [Matrix.mul_apply]
    exact Finset.sum_eq_zero fun k _ => by
      by_cases hk : d.getD b 0 ≤ k.val ∧ k.val < d.getD (b + 1) 0
      · rw [(hB b hb k j hk hj).1, mul_zero]
      · rw [(hA b hb i k hi hk).1, zero_mul]
  · rw [Matrix.mul_apply]
    exact Finset.sum_eq_zero fun k _ => by
      by_cases hk : d.getD b 0 ≤ k.val ∧ k.val < d.getD (b + 1) 0
      · rw [(hA b hb k j hk hj).2, zero_mul]
      · rw [(hB b hb i k hi hk).2, mul_zero]

theorem BlockDiag.inv {g : GL (Fin n) K} (hg : BlockDiag d (g : Matrix (Fin n) (Fin n) K)) :
    BlockDiag d ((g⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
  let B : Matrix (Fin n) (Fin n) K := ((g⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)
  change BlockDiag d B
  intro b hb i j hi hj
  have hA : (g : Matrix (Fin n) (Fin n) K) * B = 1 := by
    change (g : Matrix (Fin n) (Fin n) K) *
      ((g⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = 1
    rw [← Matrix.GeneralLinearGroup.coe_mul, mul_inv_cancel, Matrix.GeneralLinearGroup.coe_one]
  have hB : B * (g : Matrix (Fin n) (Fin n) K) = 1 := by
    change ((g⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
      (g : Matrix (Fin n) (Fin n) K) = 1
    rw [← Matrix.GeneralLinearGroup.coe_mul, inv_mul_cancel, Matrix.GeneralLinearGroup.coe_one]
  have hcomm := plr_blockProj_comm (K := K) (d := d) hg hb
  have hcomm' : plr_blockProj (K := K) n (d.getD b 0) (d.getD (b + 1) 0) * B =
      B * plr_blockProj (K := K) n (d.getD b 0) (d.getD (b + 1) 0) :=
    plr_blockProj_comm_inv (K := K) (d := d) hA hB hb hcomm
  constructor
  · have h1 : ((plr_blockProj (K := K) n (d.getD b 0) (d.getD (b + 1) 0) :
        Matrix (Fin n) (Fin n) K) * B) i j = B i j := by
      rw [plr_blockProj, Matrix.diagonal_mul, if_pos hi, one_mul]
    have h2 : (B * (plr_blockProj (K := K) n (d.getD b 0) (d.getD (b + 1) 0) :
        Matrix (Fin n) (Fin n) K)) i j = 0 := by
      rw [plr_blockProj, Matrix.mul_diagonal, if_neg hj, mul_zero]
    rw [← h1, hcomm', h2]
  · have h1 : ((plr_blockProj (K := K) n (d.getD b 0) (d.getD (b + 1) 0) :
        Matrix (Fin n) (Fin n) K) * B) j i = 0 := by
      rw [plr_blockProj, Matrix.diagonal_mul, if_neg hj, zero_mul]
    have h2 : (B * (plr_blockProj (K := K) n (d.getD b 0) (d.getD (b + 1) 0) :
        Matrix (Fin n) (Fin n) K)) j i = B j i := by
      rw [plr_blockProj, Matrix.mul_diagonal, if_pos hi, mul_one]
    rw [← h2, ← hcomm', h1]

theorem BlockDiag.stabV {g : GL (Fin n) K} (hd : IsCut n d)
    (hg : BlockDiag d (g : Matrix (Fin n) (Fin n) K)) :
    ∀ i, i < d.length → (Vsub n (d.getD i 0)).map (glLin g).toLinearMap = Vsub n (d.getD i 0) := by
  intro i hi
  refine Submodule.eq_of_le_of_finrank_eq ?_ ?_
  · rintro v ⟨w, hw, rfl⟩ j hj
    change (glLin g w) j = 0
    rw [glLin_apply, Matrix.mulVec_apply_eq_sum]
    exact Finset.sum_eq_zero fun k _ => by
      by_cases hk : k.val < d.getD i 0
      · have hb : plr_cutBlock d k.val + 1 ≤ i := plr_cutBlock_add_one_le_of_lt hd hi hk
        have hbl : plr_cutBlock d k.val + 1 < d.length := by omega
        have hkin : d.getD (plr_cutBlock d k.val) 0 ≤ k.val ∧
            k.val < d.getD (plr_cutBlock d k.val + 1) 0 :=
          ⟨plr_cutBlock_le hd k.val, plr_lt_cutBlock_succ hd k.isLt⟩
        have hjout : ¬ (d.getD (plr_cutBlock d k.val) 0 ≤ j.val ∧
            j.val < d.getD (plr_cutBlock d k.val + 1) 0) := by
          intro hcon
          have hle : d.getD (plr_cutBlock d k.val + 1) 0 ≤ d.getD i 0 :=
            plr_getD_mono hd (plr_cutBlock d k.val + 1) hb (by omega)
          omega
        rw [(hg (plr_cutBlock d k.val) hbl k j hkin hjout).2, zero_mul]
      · rw [hw k (le_of_not_gt hk), mul_zero]
  · rw [LinearEquiv.finrank_map_eq, finrank_Vsub (plr_getD_le hd hi)]

end CFSG.ClassicalInvolution.Phan.PhanE.Flag

end
