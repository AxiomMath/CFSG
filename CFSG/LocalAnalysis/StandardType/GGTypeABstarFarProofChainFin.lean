module

public import CFSG.LocalAnalysis.StandardType.GGTypeABstarFarProofChainEnd

public section

namespace CFSG.StandardType

section FinChain

variable {β : Type*} [DecidableEq β]

@[expose] def finTrunc (n c : ℕ) : Fin (n + 1) := ⟨min c n, Nat.lt_succ_of_le (min_le_right c n)⟩

theorem finTrunc_val_of_le {n c : ℕ} (h : c ≤ n) : (finTrunc n c).val = c := by
  simp [finTrunc, min_eq_left h]

theorem chain_swap_zero {n : ℕ} (ρ : Equiv.Perm (Fin (n + 1)) →* Equiv.Perm β) (w : ℕ → β)
    (hw : ∀ c d, c ≤ n → d ≤ n → w c = w d → c = d)
    (hs : ∀ c, c < n →
      ρ (Equiv.swap (finTrunc n c) (finTrunc n (c + 1))) = Equiv.swap (w c) (w (c + 1))) :
    ∀ k, 1 ≤ k → k ≤ n →
      ρ (Equiv.swap (finTrunc n 0) (finTrunc n k)) = Equiv.swap (w 0) (w k) := by
  intro k hk1
  refine Nat.le_induction (m := 1) (P := fun k _ => k ≤ n →
      ρ (Equiv.swap (finTrunc n 0) (finTrunc n k)) = Equiv.swap (w 0) (w k)) ?_ ?_ k hk1
  · intro _
    simpa using hs 0 (by omega)
  · intro k hk1 IH hkn
    have hne_f : ∀ {a b : ℕ}, a ≤ n → b ≤ n → a ≠ b → finTrunc n a ≠ finTrunc n b := by
      intro a b ha hb hab h
      exact hab (by
        have := congrArg Fin.val h
        rwa [finTrunc_val_of_le ha, finTrunc_val_of_le hb] at this)
    have h0k : finTrunc n 0 ≠ finTrunc n k := hne_f (by omega) (by omega) (by omega)
    have h0k1 : finTrunc n 0 ≠ finTrunc n (k+1) := hne_f (by omega) (by omega) (by omega)
    have hbraid : Equiv.swap (finTrunc n k) (finTrunc n (k+1))
        * Equiv.swap (finTrunc n 0) (finTrunc n k)
        * Equiv.swap (finTrunc n k) (finTrunc n (k+1))
        = Equiv.swap (finTrunc n (k+1)) (finTrunc n 0) :=
      Equiv.swap_mul_swap_mul_swap h0k h0k1
    have hb := congrArg ρ hbraid
    simp only [map_mul] at hb
    simp only [hs k (by omega), IH (by omega)] at hb
    have hw0k : w 0 ≠ w k := fun h => by have := hw 0 k (by omega) (by omega) h; omega
    have hw0k1 : w 0 ≠ w (k+1) :=
      fun h => by have := hw 0 (k+1) (by omega) (by omega) h; omega
    have hwbraid : Equiv.swap (w k) (w (k+1)) * Equiv.swap (w 0) (w k)
        * Equiv.swap (w k) (w (k+1)) = Equiv.swap (w (k+1)) (w 0) :=
      Equiv.swap_mul_swap_mul_swap hw0k hw0k1
    rw [hwbraid] at hb
    rw [Equiv.swap_comm (finTrunc n 0) (finTrunc n (k+1)), ← hb,
      Equiv.swap_comm (w (k+1)) (w 0)]

private theorem bfChainFin_swap_braid {α : Type*} [DecidableEq α] {a b c : α}
    (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c) :
    (Equiv.swap a b * Equiv.swap b c) ^ 3 = 1 := by
  have h1 : Equiv.swap a b * Equiv.swap b c * Equiv.swap a b = Equiv.swap a c := by
    simpa only [Equiv.swap_comm b a, Equiv.swap_comm c b] using
      Equiv.swap_mul_swap_mul_swap (x := c) (y := b) (z := a) hbc.symm hac.symm
  have h2 : Equiv.swap b c * Equiv.swap a b * Equiv.swap b c = Equiv.swap c a :=
    Equiv.swap_mul_swap_mul_swap (x := a) (y := b) (z := c) hab hac
  have hcube : (Equiv.swap a b * Equiv.swap b c) ^ 3
      = (Equiv.swap a b * Equiv.swap b c * Equiv.swap a b)
        * (Equiv.swap b c * Equiv.swap a b * Equiv.swap b c) := by
    simp only [pow_succ, pow_one, pow_zero, one_mul, mul_assoc]
  rw [hcube, h1, h2, Equiv.swap_comm c a, Equiv.swap_mul_self]

private theorem bfChainFin_swap_braid' {α : Type*} [DecidableEq α] {a b c : α}
    (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c) :
    (Equiv.swap b c * Equiv.swap a b) ^ 3 = 1 := by
  have h := bfChainFin_swap_braid (a := a) (b := b) (c := c) hab hbc hac
  have hinv : Equiv.swap b c * Equiv.swap a b = (Equiv.swap a b * Equiv.swap b c)⁻¹ := by
    rw [mul_inv_rev, Equiv.swap_inv, Equiv.swap_inv]
  rw [hinv, inv_pow, h, inv_one]

private theorem bfChainFin_swap_commute {α : Type*} [DecidableEq α] {a b c d : α}
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) :
    Equiv.swap a b * Equiv.swap c d = Equiv.swap c d * Equiv.swap a b := by
  have hdisj : Equiv.Perm.Disjoint (Equiv.swap a b) (Equiv.swap c d) := by
    intro x
    by_cases hxab : x = a ∨ x = b
    · right
      rcases hxab with rfl | rfl
      · exact Equiv.swap_apply_of_ne_of_ne hac had
      · exact Equiv.swap_apply_of_ne_of_ne hbc hbd
    · simp only [not_or] at hxab
      left
      exact Equiv.swap_apply_of_ne_of_ne hxab.1 hxab.2
  exact hdisj.commute

theorem ggFar_chain_commute {n : ℕ} (hn : 3 ≤ n)
    (ρ₁ ρ₂ : Equiv.Perm (Fin (n + 1)) →* Equiv.Perm β)
    (hρ₁ : Function.Injective ρ₁) (hρ₂ : Function.Injective ρ₂)
    (hs₁ : ∀ c d : Fin (n + 1), c ≠ d → (ρ₁ (Equiv.swap c d)).IsSwap)
    (hs₂ : ∀ c d : Fin (n + 1), c ≠ d → (ρ₂ (Equiv.swap c d)).IsSwap)
    (hJ : ∀ i j : Fin n,
      ρ₁ (Equiv.swap i.succ j.succ) = ρ₂ (Equiv.swap i.castSucc j.castSucc))
    {i j : Fin n} (hi : i.val = 0) (hj : j.val + 1 = n)
    (hout : ∀ σ, ρ₁ σ ≠ ρ₂ (Equiv.swap j.castSucc j.succ)) :
    ρ₁ (Equiv.swap i.castSucc i.succ) * ρ₂ (Equiv.swap j.castSucc j.succ) =
      ρ₂ (Equiv.swap j.castSucc j.succ) * ρ₁ (Equiv.swap i.castSucc i.succ) := by
  have hne_fin : ∀ c d : ℕ, c ≤ n → d ≤ n → c ≠ d → finTrunc n c ≠ finTrunc n d := by
    intro c d hc hd hcd h
    exact hcd (by
      have := congrArg Fin.val h
      rwa [finTrunc_val_of_le hc, finTrunc_val_of_le hd] at this)
  have hi0 : (i.castSucc : Fin (n + 1)) = finTrunc n 0 := by
    apply Fin.ext
    rw [Fin.val_castSucc, hi]
    exact (finTrunc_val_of_le (n := n) (c := 0) (Nat.zero_le n)).symm
  have hi1 : (i.succ : Fin (n + 1)) = finTrunc n 1 := by
    apply Fin.ext
    rw [Fin.val_succ, hi]
    simpa using (finTrunc_val_of_le (n := n) (c := 1) (by omega)).symm
  have hj0 : (j.castSucc : Fin (n + 1)) = finTrunc n (n - 1) := by
    apply Fin.ext
    rw [Fin.val_castSucc, finTrunc_val_of_le (n := n) (c := n - 1) (by omega)]
    omega
  have hj1 : (j.succ : Fin (n + 1)) = finTrunc n n := by
    apply Fin.ext
    rw [Fin.val_succ, finTrunc_val_of_le (n := n) (c := n) (le_refl n)]
    exact hj
  let s : ℕ → Equiv.Perm β := fun c => ρ₁ (Equiv.swap (finTrunc n c) (finTrunc n (c+1)))
  have hsw : ∀ c, c < n → (s c).IsSwap := by
    intro c hc
    exact hs₁ _ _ (hne_fin c (c+1) (by omega) (by omega) (by omega))
  have hne : ∀ c d, c < d → d < n → s c ≠ s d := by
    intro c d hcd hdn heq
    have h1 : Equiv.swap (finTrunc n c) (finTrunc n (c+1))
        = Equiv.swap (finTrunc n d) (finTrunc n (d+1)) := hρ₁ heq
    have h2 := congrArg (fun e : Equiv.Perm (Fin (n+1)) => e (finTrunc n c)) h1
    rw [Equiv.swap_apply_left,
        Equiv.swap_apply_of_ne_of_ne (hne_fin c d (by omega) (by omega) (by omega))
          (hne_fin c (d+1) (by omega) (by omega) (by omega))] at h2
    have h3 := congrArg Fin.val h2
    rw [finTrunc_val_of_le (n := n) (c := c+1) (by omega),
        finTrunc_val_of_le (n := n) (c := c) (by omega)] at h3
    omega
  have hbr : ∀ c, c + 1 < n → (s c * s (c+1)) ^ 3 = 1 := by
    intro c hc
    have hmap : s c * s (c+1)
        = ρ₁ (Equiv.swap (finTrunc n c) (finTrunc n (c+1))
            * Equiv.swap (finTrunc n (c+1)) (finTrunc n (c+2))) := by
      change ρ₁ (Equiv.swap (finTrunc n c) (finTrunc n (c+1)))
          * ρ₁ (Equiv.swap (finTrunc n (c+1)) (finTrunc n (c+2)))
        = ρ₁ (Equiv.swap (finTrunc n c) (finTrunc n (c+1))
            * Equiv.swap (finTrunc n (c+1)) (finTrunc n (c+2)))
      rw [map_mul]
    rw [hmap, ← map_pow]
    have hb : (Equiv.swap (finTrunc n c) (finTrunc n (c+1))
        * Equiv.swap (finTrunc n (c+1)) (finTrunc n (c+2))) ^ 3 = 1 :=
      bfChainFin_swap_braid (a := finTrunc n c) (b := finTrunc n (c+1))
        (c := finTrunc n (c+2))
        (hne_fin c (c+1) (by omega) (by omega) (by omega))
        (hne_fin (c+1) (c+2) (by omega) (by omega) (by omega))
        (hne_fin c (c+2) (by omega) (by omega) (by omega))
    rw [hb, map_one]
  have hcomm : ∀ c d, c + 2 ≤ d → d < n → s c * s d = s d * s c := by
    intro c d hcd hdn
    have hdisj : Equiv.swap (finTrunc n c) (finTrunc n (c+1))
        * Equiv.swap (finTrunc n d) (finTrunc n (d+1))
        = Equiv.swap (finTrunc n d) (finTrunc n (d+1))
          * Equiv.swap (finTrunc n c) (finTrunc n (c+1)) :=
      bfChainFin_swap_commute
        (hne_fin c (c+1) (by omega) (by omega) (by omega))
        (hne_fin c d (by omega) (by omega) (by omega))
        (hne_fin c (d+1) (by omega) (by omega) (by omega))
        (hne_fin (c+1) d (by omega) (by omega) (by omega))
        (hne_fin (c+1) (d+1) (by omega) (by omega) (by omega))
        (hne_fin d (d+1) (by omega) (by omega) (by omega))
    have hmap : ρ₁ (Equiv.swap (finTrunc n c) (finTrunc n (c+1)))
          * ρ₁ (Equiv.swap (finTrunc n d) (finTrunc n (d+1)))
        = ρ₁ (Equiv.swap (finTrunc n d) (finTrunc n (d+1)))
          * ρ₁ (Equiv.swap (finTrunc n c) (finTrunc n (c+1))) := by
      rw [← map_mul, ← map_mul, hdisj]
    exact hmap
  obtain ⟨w, hw, hsw_rep⟩ := chain_labels s n (by omega) hsw hne hbr hcomm
  have hsw_rep' : ∀ c, c < n →
      ρ₁ (Equiv.swap (finTrunc n c) (finTrunc n (c+1))) = Equiv.swap (w c) (w (c+1)) := by
    intro c hc
    exact hsw_rep c hc
  have hJkey : ∀ c, 1 ≤ c → c < n →
      ρ₁ (Equiv.swap (finTrunc n c) (finTrunc n (c+1)))
        = ρ₂ (Equiv.swap (finTrunc n (c-1)) (finTrunc n c)) := by
    intro c hc1 hcn
    let i' : Fin n := ⟨c - 1, by omega⟩
    let j' : Fin n := ⟨c, hcn⟩
    have e1 : i'.succ = finTrunc n c := by
      apply Fin.ext
      rw [Fin.val_succ, finTrunc_val_of_le (n := n) (c := c) (by omega)]
      dsimp only [i']
      omega
    have e2 : j'.succ = finTrunc n (c+1) := by
      apply Fin.ext
      rw [Fin.val_succ, finTrunc_val_of_le (n := n) (c := c+1) (by omega)]
    have e3 : i'.castSucc = finTrunc n (c-1) := by
      apply Fin.ext
      rw [Fin.val_castSucc]
      dsimp only [i']
      exact (finTrunc_val_of_le (n := n) (c := c-1) (by omega)).symm
    have e4 : j'.castSucc = finTrunc n c := by
      apply Fin.ext
      rw [Fin.val_castSucc]
      dsimp only [j']
      exact (finTrunc_val_of_le (n := n) (c := c) (by omega)).symm
    have hJc := hJ i' j'
    rw [e1, e2, e3, e4] at hJc
    exact hJc
  have hzero : ρ₁ (Equiv.swap (finTrunc n 0) (finTrunc n n)) = Equiv.swap (w 0) (w n) :=
    chain_swap_zero (n := n) ρ₁ w hw hsw_rep' n (by omega) (le_refl n)
  have hσ : (ρ₂ (Equiv.swap j.castSucc j.succ)).IsSwap :=
    hs₂ j.castSucc j.succ (ne_of_lt (Fin.castSucc_lt_succ (i := j)))
  have hne_end : ∀ c, 1 ≤ c → c < n →
      ρ₂ (Equiv.swap j.castSucc j.succ) ≠ Equiv.swap (w c) (w (c+1)) := by
    intro c hc1 hcn heq
    have hwc : Equiv.swap (w c) (w (c+1))
        = ρ₂ (Equiv.swap (finTrunc n (c-1)) (finTrunc n c)) := by
      rw [← hsw_rep' c hcn]
      exact hJkey c hc1 hcn
    have hσ' : ρ₂ (Equiv.swap j.castSucc j.succ)
        = ρ₂ (Equiv.swap (finTrunc n (c-1)) (finTrunc n c)) := by
      rw [heq, hwc]
    have hfin := hρ₂ hσ'
    have hval := congrArg (fun e : Equiv.Perm (Fin (n+1)) => e (finTrunc n n)) hfin
    rw [hj0, hj1] at hval
    rw [Equiv.swap_apply_right,
        Equiv.swap_apply_of_ne_of_ne (hne_fin n (c-1) (by omega) (by omega) (by omega))
          (hne_fin n c (by omega) (by omega) (by omega))] at hval
    have hvl := congrArg Fin.val hval
    rw [finTrunc_val_of_le (n := n) (c := n-1) (by omega),
        finTrunc_val_of_le (n := n) (c := n) (le_refl n)] at hvl
    omega
  have hcomm_end : ∀ c, 1 ≤ c → c + 2 ≤ n →
      ρ₂ (Equiv.swap j.castSucc j.succ) * Equiv.swap (w c) (w (c+1))
        = Equiv.swap (w c) (w (c+1)) * ρ₂ (Equiv.swap j.castSucc j.succ) := by
    intro c hc1 hc2
    have hwc : Equiv.swap (w c) (w (c+1))
        = ρ₂ (Equiv.swap (finTrunc n (c-1)) (finTrunc n c)) := by
      rw [← hsw_rep' c (by omega)]
      exact hJkey c hc1 (by omega)
    have hdisj : Equiv.swap (finTrunc n (n-1)) (finTrunc n n)
        * Equiv.swap (finTrunc n (c-1)) (finTrunc n c)
        = Equiv.swap (finTrunc n (c-1)) (finTrunc n c)
          * Equiv.swap (finTrunc n (n-1)) (finTrunc n n) :=
      bfChainFin_swap_commute
        (hne_fin (n-1) n (by omega) (by omega) (by omega))
        (hne_fin (n-1) (c-1) (by omega) (by omega) (by omega))
        (hne_fin (n-1) c (by omega) (by omega) (by omega))
        (hne_fin n (c-1) (by omega) (by omega) (by omega))
        (hne_fin n c (by omega) (by omega) (by omega))
        (hne_fin (c-1) c (by omega) (by omega) (by omega))
    have hmap : ρ₂ (Equiv.swap (finTrunc n (n-1)) (finTrunc n n))
          * ρ₂ (Equiv.swap (finTrunc n (c-1)) (finTrunc n c))
        = ρ₂ (Equiv.swap (finTrunc n (c-1)) (finTrunc n c))
          * ρ₂ (Equiv.swap (finTrunc n (n-1)) (finTrunc n n)) := by
      rw [← map_mul, ← map_mul, hdisj]
    rw [hj0, hj1, hwc]
    exact hmap
  have hbr_end :
      (ρ₂ (Equiv.swap j.castSucc j.succ) * Equiv.swap (w (n-1)) (w n)) ^ 3 = 1 := by
    have hlast : Equiv.swap (w (n-1)) (w n)
        = ρ₂ (Equiv.swap (finTrunc n (n-2)) (finTrunc n (n-1))) := by
      have hs' := hsw_rep' (n-1) (by omega)
      rw [show (n-1)+1 = n by omega] at hs'
      have hk := hJkey (n-1) (by omega) (by omega)
      rw [show (n-1)+1 = n by omega, show (n-1)-1 = n-2 by omega] at hk
      rw [← hs']
      exact hk
    rw [hj0, hj1, hlast]
    rw [← map_mul, ← map_pow]
    have hb : (Equiv.swap (finTrunc n (n-1)) (finTrunc n n)
        * Equiv.swap (finTrunc n (n-2)) (finTrunc n (n-1))) ^ 3 = 1 :=
      bfChainFin_swap_braid' (a := finTrunc n (n-2)) (b := finTrunc n (n-1))
        (c := finTrunc n n)
        (hne_fin (n-2) (n-1) (by omega) (by omega) (by omega))
        (hne_fin (n-1) n (by omega) (by omega) (by omega))
        (hne_fin (n-2) n (by omega) (by omega) (by omega))
    rw [hb, map_one]
  have hloop : ρ₂ (Equiv.swap j.castSucc j.succ) ≠ Equiv.swap (w 0) (w n) := by
    rw [← hzero]
    exact (hout (Equiv.swap (finTrunc n 0) (finTrunc n n))).symm
  have hcommute :=
    chain_end_commute (n := n) hn w hw hσ hne_end hcomm_end hbr_end hloop
  have h01 : ρ₁ (Equiv.swap (finTrunc n 0) (finTrunc n 1)) = Equiv.swap (w 0) (w 1) := by
    simpa using hsw_rep' 0 (by omega)
  rw [hi0, hi1, h01]
  exact hcommute.symm

end FinChain

end CFSG.StandardType
