module

public import CFSG.LocalAnalysis.StandardType.PhanEFlagCut

public section

namespace CFSG.ClassicalInvolution.Phan.PhanE.Flag

open Module CFSG.ClassicalInvolution.Phan.PhanE

variable {K : Type} [Field K] {n : ℕ} {d : List ℕ}

private theorem q2cFA_getD_mono {d : List ℕ} (hd : IsCut n d) (i : ℕ) :
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

private theorem q2cFA_getD_le {d : List ℕ} (hd : IsCut n d) {i : ℕ} (hi : i < d.length) :
    d.getD i 0 ≤ n := by
  have h := q2cFA_getD_mono hd i (show i ≤ d.length - 1 by omega) le_rfl
  rwa [hd.last] at h

private def q2cFA_cutBlock (d : List ℕ) (j : ℕ) : ℕ :=
  Nat.findGreatest (fun b => d.getD b 0 ≤ j) (d.length - 1)

private theorem q2cFA_cutBlock_le {d : List ℕ} (hd : IsCut n d) (j : ℕ) :
    d.getD (q2cFA_cutBlock d j) 0 ≤ j :=
  Nat.findGreatest_spec (P := fun b => d.getD b 0 ≤ j) (m := 0) (n := d.length - 1)
    (Nat.zero_le _) (by rw [hd.head]; exact Nat.zero_le j)

private theorem q2cFA_cutBlock_lt_of_lt {d : List ℕ} (hd : IsCut n d) {j : ℕ} (hj : j < n) :
    q2cFA_cutBlock d j < d.length - 1 := by
  have hle := q2cFA_cutBlock_le hd j
  have hbnd : q2cFA_cutBlock d j ≤ d.length - 1 := Nat.findGreatest_le _
  by_contra h
  rw [show q2cFA_cutBlock d j = d.length - 1 from by omega, hd.last] at hle
  omega

private theorem q2cFA_lt_cutBlock_succ {d : List ℕ} (hd : IsCut n d) {j : ℕ} (hj : j < n) :
    j < d.getD (q2cFA_cutBlock d j + 1) 0 := by
  have hb := q2cFA_cutBlock_lt_of_lt hd hj; by_contra h
  exact (Nat.findGreatest_eq_iff (P := fun b => d.getD b 0 ≤ j) (k := d.length - 1)).1 rfl
    |>.2.2 (Nat.lt_succ_self _) (Nat.succ_le_iff.mpr hb) (le_of_not_gt h)

private theorem q2cFA_cutBlock_eq_self {d : List ℕ} (hd : IsCut n d) {b j : ℕ}
    (hb : b + 1 < d.length) (h1 : d.getD b 0 ≤ j) (h2 : j < d.getD (b + 1) 0) :
    q2cFA_cutBlock d j = b := by
  refine (Nat.findGreatest_eq_iff (P := fun b => d.getD b 0 ≤ j) (k := d.length - 1)).2
    ⟨by omega, fun _ => h1, ?_⟩
  intro b' hbb' hb'k hPb'
  have hmono := q2cFA_getD_mono hd (b + 1) (show b + 1 ≤ b' by omega) hb'k
  omega

private theorem q2cFA_S_zero (hd : IsCut n d) {S : ℕ → ℕ → Submodule K (Fin n → K)}
    (hlo : ∀ b s, b + 1 < d.length → s ≤ blockSize d b → Vsub n (d.getD b 0) ≤ S b s)
    (hdim : ∀ b s, b + 1 < d.length → s ≤ blockSize d b →
      finrank K (S b s) = d.getD b 0 + s)
    {b : ℕ} (hb : b + 1 < d.length) : S b 0 = Vsub n (d.getD b 0) := by
  have hbn : d.getD b 0 ≤ n := q2cFA_getD_le hd (by omega)
  exact (Submodule.eq_of_le_of_finrank_eq (hlo b 0 hb (Nat.zero_le _))
    (by rw [finrank_Vsub hbn, hdim b 0 hb (Nat.zero_le _)]; omega)).symm

private theorem q2cFA_S_last (hd : IsCut n d) {S : ℕ → ℕ → Submodule K (Fin n → K)}
    (hhi : ∀ b s, b + 1 < d.length → s ≤ blockSize d b →
      S b s ≤ Vsub n (d.getD (b + 1) 0))
    (hdim : ∀ b s, b + 1 < d.length → s ≤ blockSize d b →
      finrank K (S b s) = d.getD b 0 + s)
    {b : ℕ} (hb : b + 1 < d.length) :
    S b (blockSize d b) = Vsub n (d.getD (b + 1) 0) := by
  have hbn : d.getD (b + 1) 0 ≤ n := q2cFA_getD_le hd hb
  have hle : d.getD b 0 ≤ d.getD (b + 1) 0 := (hd.strict b hb).le
  refine Submodule.eq_of_le_of_finrank_eq (hhi b (blockSize d b) hb le_rfl) ?_
  rw [hdim b (blockSize d b) hb le_rfl, finrank_Vsub hbn]
  simp only [blockSize]
  omega

theorem exists_flag_of_blocks (hd : IsCut n d) (S : ℕ → ℕ → Submodule K (Fin n → K))
    (hlo : ∀ b s, b + 1 < d.length → s ≤ blockSize d b → Vsub n (d.getD b 0) ≤ S b s)
    (hhi : ∀ b s, b + 1 < d.length → s ≤ blockSize d b → S b s ≤ Vsub n (d.getD (b + 1) 0))
    (hmono : ∀ b s s', b + 1 < d.length → s ≤ s' → s' ≤ blockSize d b → S b s ≤ S b s')
    (hdim : ∀ b s, b + 1 < d.length → s ≤ blockSize d b →
      finrank K (S b s) = d.getD b 0 + s) :
    ∃ z ∈ refSet K n d, ∀ b s, b + 1 < d.length → s ≤ blockSize d b →
      z.E (d.getD b 0 + s) = S b s := by
  let yE : ℕ → Submodule K (Fin n → K) := fun j =>
    if j < n then S (q2cFA_cutBlock d j) (j - d.getD (q2cFA_cutBlock d j) 0) else Vsub n n
  have hyE : ∀ j, yE j = if j < n then S (q2cFA_cutBlock d j)
      (j - d.getD (q2cFA_cutBlock d j) 0) else Vsub n n := fun _ => rfl
  have hyE_cut : ∀ i, i < d.length → yE (d.getD i 0) = Vsub n (d.getD i 0) := by
    intro i hi
    by_cases hin : d.getD i 0 < n
    · have hi1 : i + 1 < d.length := by
        by_contra h
        rw [show i = d.length - 1 from by omega, hd.last] at hin
        omega
      rw [hyE, if_pos hin, q2cFA_cutBlock_eq_self hd hi1 le_rfl (hd.strict i hi1),
        Nat.sub_self, q2cFA_S_zero hd hlo hdim hi1]
    · rw [show d.getD i 0 = n from by have := q2cFA_getD_le hd hi; omega, hyE,
        if_neg (by omega : ¬ n < n)]
  have hmain : ∀ b s, b + 1 < d.length → s ≤ blockSize d b →
      yE (d.getD b 0 + s) = S b s := by
    intro b s hb hs
    have hb' : b < d.length := by omega
    have hle : d.getD b 0 ≤ d.getD (b + 1) 0 := (hd.strict b hb).le
    have hbn : d.getD (b + 1) 0 ≤ n := q2cFA_getD_le hd hb
    by_cases hsm : s = blockSize d b
    · subst hsm
      rw [show d.getD b 0 + blockSize d b = d.getD (b + 1) 0 by
        simp only [blockSize]; omega,
        hyE_cut (b + 1) hb, q2cFA_S_last hd hhi hdim hb]
    · have hslt : s < blockSize d b := lt_of_le_of_ne hs hsm
      have hjn : d.getD b 0 + s < n := by
        have := hbn; simp only [blockSize] at hslt; omega
      rw [hyE, if_pos hjn,
        q2cFA_cutBlock_eq_self hd hb (j := d.getD b 0 + s) (Nat.le_add_right _ _)
          (by have h := hslt; simp only [blockSize] at h; omega),
        show d.getD b 0 + s - d.getD b 0 = s by omega]
  have hmonoE : Monotone yE := by
    refine monotone_nat_of_le_succ fun j => ?_
    by_cases hjn : j + 1 < n
    · have hj : j < n := by omega
      rw [hyE, hyE, if_pos hj, if_pos hjn]
      by_cases heq : q2cFA_cutBlock d j = q2cFA_cutBlock d (j + 1)
      · rw [heq]
        have hb1 : q2cFA_cutBlock d (j + 1) + 1 < d.length := by
          have := q2cFA_cutBlock_lt_of_lt hd hjn; omega
        have hlt := q2cFA_lt_cutBlock_succ hd hjn
        have hcle := q2cFA_cutBlock_le hd (j + 1)
        exact hmono (q2cFA_cutBlock d (j + 1)) (j - d.getD (q2cFA_cutBlock d (j + 1)) 0)
          (j + 1 - d.getD (q2cFA_cutBlock d (j + 1)) 0) hb1 (by omega)
          (by simp only [blockSize] at hlt ⊢; omega)
      · have hbb' : q2cFA_cutBlock d j ≤ q2cFA_cutBlock d (j + 1) :=
          Nat.le_findGreatest (Nat.findGreatest_le _)
            (le_trans (q2cFA_cutBlock_le hd j) (Nat.le_succ j))
        have hltc : q2cFA_cutBlock d j < q2cFA_cutBlock d (j + 1) := lt_of_le_of_ne hbb' heq
        have hb1 : q2cFA_cutBlock d j + 1 < d.length := by
          have := q2cFA_cutBlock_lt_of_lt hd hj; omega
        have hb2 : q2cFA_cutBlock d (j + 1) + 1 < d.length := by
          have := q2cFA_cutBlock_lt_of_lt hd hjn; omega
        have hlt1 := q2cFA_lt_cutBlock_succ hd hj
        have hlt2 := q2cFA_lt_cutBlock_succ hd hjn
        have hcle1 := q2cFA_cutBlock_le hd j
        have hcle2 := q2cFA_cutBlock_le hd (j + 1)
        refine le_trans (hhi (q2cFA_cutBlock d j) (j - d.getD (q2cFA_cutBlock d j) 0) hb1
            (by simp only [blockSize]; omega))
          (le_trans (Vsub_mono (q2cFA_getD_mono hd (q2cFA_cutBlock d j + 1)
              (show q2cFA_cutBlock d j + 1 ≤ q2cFA_cutBlock d (j + 1) by omega)
              (Nat.findGreatest_le _)))
            (hlo (q2cFA_cutBlock d (j + 1)) (j + 1 - d.getD (q2cFA_cutBlock d (j + 1)) 0)
              hb2 (by simp only [blockSize]; omega)))
    · have htop : yE (j + 1) = ⊤ := by
        rw [hyE, if_neg (by omega : ¬ j + 1 < n), Vsub_self]
      rw [htop]
      exact le_top
  have hdimE : ∀ j, j ≤ n → finrank K (yE j) = j := by
    intro j hj
    by_cases hjn : j < n
    · rw [hyE, if_pos hjn]
      have hb : q2cFA_cutBlock d j + 1 < d.length := by
        have := q2cFA_cutBlock_lt_of_lt hd hjn; omega
      have hcle := q2cFA_cutBlock_le hd j
      have hlt := q2cFA_lt_cutBlock_succ hd hjn
      rw [hdim (q2cFA_cutBlock d j) (j - d.getD (q2cFA_cutBlock d j) 0) hb
        (by simp only [blockSize] at hlt ⊢; omega)]
      omega
    · rw [hyE, if_neg hjn, show j = n from by omega, finrank_Vsub le_rfl]
  refine ⟨⟨yE, hmonoE, hdimE, fun j hj => by
    rw [hyE, if_neg (by omega : ¬ j < n), Vsub_self]⟩, hyE_cut, hmain⟩

end CFSG.ClassicalInvolution.Phan.PhanE.Flag
