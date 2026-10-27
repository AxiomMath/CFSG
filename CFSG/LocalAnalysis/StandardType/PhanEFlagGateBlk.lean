module

public import CFSG.LocalAnalysis.StandardType.PhanEFlagCut

public section

namespace CFSG.ClassicalInvolution.Phan.PhanE.Flag

open Module CFSG.Monster.B.Geometry CFSG.LieType.Chevalley.CosetBuilding
  CFSG.ClassicalInvolution.Phan.PhanE

variable {K : Type} [Field K] {n m : ℕ} {d : List ℕ}

theorem q2cFG_mono (hd : IsCut n d) {i j : ℕ} (hij : i ≤ j) (hj : j < d.length) :
    d.getD i 0 ≤ d.getD j 0 := by
  induction j with
  | zero =>
      have h : i = 0 := Nat.eq_zero_of_le_zero hij
      subst h
      rfl
  | succ j ih =>
      rcases Nat.eq_or_lt_of_le hij with heq | hlt
      · subst heq; rfl
      · exact le_trans (ih (by omega) (by omega)) (le_of_lt (hd.strict j (by omega)))

theorem q2cFG_le_n (hd : IsCut n d) {i : ℕ} (hi : i < d.length) :
    d.getD i 0 ≤ n := by
  have h := q2cFG_mono hd (show i ≤ d.length - 1 by omega) (by omega)
  rwa [hd.last] at h

theorem q2cFG_hmono (hd : IsCut n d) :
    ∀ i, i + 1 < d.length → d.getD i 0 ≤ d.getD (i + 1) 0 :=
  fun i hi => le_of_lt (hd.strict i hi)

private theorem q2cFG_exists_block (hd : IsCut n d) {p : ℕ} (hp : p < n) :
    ∃ i, p < d.getD i 0 :=
  ⟨d.length - 1, by rw [hd.last]; exact hp⟩

noncomputable def q2cFG_blk (hd : IsCut n d) (p : ℕ) (hp : p < n) : ℕ :=
  Nat.find (q2cFG_exists_block hd hp) - 1

theorem q2cFG_blk_lt (hd : IsCut n d) (p : ℕ) (hp : p < n) :
    q2cFG_blk hd p hp + 1 < d.length := by
  have hspec := Nat.find_spec (q2cFG_exists_block hd hp)
  have hle : Nat.find (q2cFG_exists_block hd hp) ≤ d.length - 1 :=
    Nat.find_le (show p < d.getD (d.length - 1) 0 by rw [hd.last]; exact hp)
  have hi1 : 1 ≤ Nat.find (q2cFG_exists_block hd hp) := by
    rw [Nat.one_le_iff_ne_zero]
    intro h0
    rw [h0, hd.head] at hspec
    omega
  have hpos : 0 < d.length :=
    lt_of_lt_of_le Nat.zero_lt_one (le_trans hi1 (le_trans hle (Nat.sub_le _ _)))
  unfold q2cFG_blk
  rw [Nat.sub_add_cancel hi1]
  exact lt_of_le_of_lt hle (Nat.sub_one_lt_of_lt hpos)

theorem q2cFG_blk_le (hd : IsCut n d) (p : ℕ) (hp : p < n) :
    d.getD (q2cFG_blk hd p hp) 0 ≤ p := by
  have hspec := Nat.find_spec (q2cFG_exists_block hd hp)
  have hne : Nat.find (q2cFG_exists_block hd hp) ≠ 0 := by
    intro h0
    rw [h0, hd.head] at hspec
    omega
  have hmin := Nat.find_min (q2cFG_exists_block hd hp)
    (Nat.sub_one_lt_of_lt (Nat.pos_of_ne_zero hne))
  unfold q2cFG_blk
  omega

theorem q2cFG_blk_lt_level (hd : IsCut n d) (p : ℕ) (hp : p < n) :
    p < d.getD (q2cFG_blk hd p hp + 1) 0 := by
  have hspec : p < d.getD (Nat.find (q2cFG_exists_block hd hp)) 0 :=
    Nat.find_spec (q2cFG_exists_block hd hp)
  unfold q2cFG_blk
  rw [Nat.sub_add_cancel (by
    rw [Nat.one_le_iff_ne_zero]
    intro h0
    rw [h0, hd.head] at hspec
    omega)]
  exact hspec

private theorem q2cFG_block_unique (hd : IsCut n d) {p b b' : ℕ}
    (hb : b + 1 < d.length) (hb₁ : d.getD b 0 ≤ p) (hb₂ : p < d.getD (b + 1) 0)
    (hb' : b' + 1 < d.length) (hb'₁ : d.getD b' 0 ≤ p) (hb'₂ : p < d.getD (b' + 1) 0) :
    b = b' := by
  rcases lt_trichotomy b b' with h | h | h
  · have hmono := q2cFG_mono hd (show b + 1 ≤ b' by omega) (by omega)
    omega
  · exact h
  · have hmono := q2cFG_mono hd (show b' + 1 ≤ b by omega) (by omega)
    omega

noncomputable def q2cFG_blkFin (hd : IsCut n d) (k : Fin n) : ℕ :=
  q2cFG_blk hd (Fin.revPerm k).val (Fin.revPerm k).isLt

theorem q2cFG_blkFin_lt (hd : IsCut n d) (k : Fin n) :
    q2cFG_blkFin hd k + 1 < d.length :=
  q2cFG_blk_lt hd (Fin.revPerm k).val (Fin.revPerm k).isLt

private theorem q2cFG_blkFin_le (hd : IsCut n d) (k : Fin n) :
    d.getD (q2cFG_blkFin hd k) 0 ≤ (Fin.revPerm k).val :=
  q2cFG_blk_le hd (Fin.revPerm k).val (Fin.revPerm k).isLt

private theorem q2cFG_blkFin_lt' (hd : IsCut n d) (k : Fin n) :
    (Fin.revPerm k).val < d.getD (q2cFG_blkFin hd k + 1) 0 :=
  q2cFG_blk_lt_level hd (Fin.revPerm k).val (Fin.revPerm k).isLt

theorem q2cFG_blkFin_window (hd : IsCut n d) (k : Fin n) :
    n - d.getD (q2cFG_blkFin hd k + 1) 0 ≤ k.val ∧
      k.val < n - d.getD (q2cFG_blkFin hd k) 0 := by
  have h₁ := q2cFG_blkFin_le hd k
  have h₂ := q2cFG_blkFin_lt' hd k
  have hb := q2cFG_blkFin_lt hd k
  have hle := q2cFG_le_n hd hb
  have hk := k.isLt
  have hrev : (Fin.revPerm k).val = n - (k.val + 1) := rfl
  rw [hrev] at h₁ h₂
  constructor <;> omega

theorem q2cFG_blkFin_unique (hd : IsCut n d) (k : Fin n) {b : ℕ}
    (hb : b + 1 < d.length) (hk₁ : n - d.getD (b + 1) 0 ≤ k.val)
    (hk₂ : k.val < n - d.getD b 0) :
    q2cFG_blkFin hd k = b := by
  have hle := q2cFG_le_n hd hb
  have hk := k.isLt
  have hrev : (Fin.revPerm k).val = n - (k.val + 1) := rfl
  have hb₁ : d.getD b 0 ≤ (Fin.revPerm k).val := by rw [hrev]; omega
  have hb₂ : (Fin.revPerm k).val < d.getD (b + 1) 0 := by rw [hrev]; omega
  exact q2cFG_block_unique hd (q2cFG_blkFin_lt hd k) (q2cFG_blkFin_le hd k)
    (q2cFG_blkFin_lt' hd k) hb hb₁ hb₂

@[expose] noncomputable def q2cFG_r (hd : IsCut n d) (k : Fin n) : ℕ :=
  k.val + 1 + d.getD (q2cFG_blkFin hd k + 1) 0 - n

theorem q2cFG_r_pos (hd : IsCut n d) (k : Fin n) : 1 ≤ q2cFG_r hd k := by
  have h := (q2cFG_blkFin_window hd k).1
  have hb := q2cFG_blkFin_lt hd k
  have hle := q2cFG_le_n hd hb
  unfold q2cFG_r
  omega

theorem q2cFG_r_spec (hd : IsCut n d) (k : Fin n) :
    n - d.getD (q2cFG_blkFin hd k + 1) 0 + q2cFG_r hd k = k.val + 1 := by
  have h := (q2cFG_blkFin_window hd k).1
  have hb := q2cFG_blkFin_lt hd k
  have hle := q2cFG_le_n hd hb
  unfold q2cFG_r
  omega

private noncomputable def q2cFG_rho (hd : IsCut n d) (p : Fin n) : Fin n :=
  ⟨d.getD (q2cFG_blk hd p.val p.isLt) 0 +
    d.getD (q2cFG_blk hd p.val p.isLt + 1) 0 - 1 - p.val, by
    have hb := q2cFG_blk_lt hd p.val p.isLt
    have h₁ := q2cFG_blk_le hd p.val p.isLt
    have h₂ := q2cFG_blk_lt_level hd p.val p.isLt
    have h₃ := q2cFG_le_n hd hb
    have hmono := q2cFG_hmono hd (q2cFG_blk hd p.val p.isLt) hb
    have hp := p.isLt
    omega⟩

private theorem q2cFG_rho_val (hd : IsCut n d) (p : Fin n) :
    (q2cFG_rho hd p).val = d.getD (q2cFG_blk hd p.val p.isLt) 0 +
      d.getD (q2cFG_blk hd p.val p.isLt + 1) 0 - 1 - p.val := rfl

private theorem q2cFG_rho_rho (hd : IsCut n d) (p : Fin n) :
    q2cFG_rho hd (q2cFG_rho hd p) = p := by
  apply Fin.ext
  have hb := q2cFG_blk_lt hd p.val p.isLt
  have h₁ := q2cFG_blk_le hd p.val p.isLt
  have h₂ := q2cFG_blk_lt_level hd p.val p.isLt
  have hmono := q2cFG_hmono hd (q2cFG_blk hd p.val p.isLt) hb
  have ha₁ : d.getD (q2cFG_blk hd p.val p.isLt) 0 ≤ (q2cFG_rho hd p).val := by
    rw [q2cFG_rho_val]; omega
  have ha₂ : (q2cFG_rho hd p).val < d.getD (q2cFG_blk hd p.val p.isLt + 1) 0 := by
    rw [q2cFG_rho_val]; omega
  have hblk : q2cFG_blk hd (q2cFG_rho hd p).val (q2cFG_rho hd p).isLt =
      q2cFG_blk hd p.val p.isLt :=
    q2cFG_block_unique hd
      (q2cFG_blk_lt hd (q2cFG_rho hd p).val (q2cFG_rho hd p).isLt)
      (q2cFG_blk_le hd (q2cFG_rho hd p).val (q2cFG_rho hd p).isLt)
      (q2cFG_blk_lt_level hd (q2cFG_rho hd p).val (q2cFG_rho hd p).isLt)
      hb ha₁ ha₂
  rw [q2cFG_rho_val, hblk, q2cFG_rho_val]
  omega

private noncomputable def q2cFG_rhoEquiv (hd : IsCut n d) : Equiv.Perm (Fin n) where
  toFun := q2cFG_rho hd
  invFun := q2cFG_rho hd
  left_inv := q2cFG_rho_rho hd
  right_inv := q2cFG_rho_rho hd

noncomputable def q2cFG_tau (hd : IsCut n d) : Equiv.Perm (Fin n) :=
  (Fin.revPerm : Equiv.Perm (Fin n)).trans (q2cFG_rhoEquiv hd)

theorem q2cFG_tau_val (hd : IsCut n d) (k : Fin n) :
    (q2cFG_tau hd k).val = d.getD (q2cFG_blkFin hd k) 0 + q2cFG_r hd k - 1 := by
  have hrev : (Fin.revPerm k).val = n - (k.val + 1) := rfl
  have hblk : q2cFG_blk hd (Fin.revPerm k).val (Fin.revPerm k).isLt = q2cFG_blkFin hd k := rfl
  show (q2cFG_rho hd (Fin.revPerm k)).val = _
  rw [q2cFG_rho_val, hblk, hrev]
  unfold q2cFG_r
  have hwin := (q2cFG_blkFin_window hd k).1
  have hb := q2cFG_blkFin_lt hd k
  have hle := q2cFG_le_n hd hb
  have hk := k.isLt
  omega

end CFSG.ClassicalInvolution.Phan.PhanE.Flag
