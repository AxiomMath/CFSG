module

public import Mathlib.Algebra.Order.SuccPred
public import Mathlib.Data.Sym.Sym2.Init
public import Mathlib.GroupTheory.Perm.Support
public import Mathlib.Tactic.NormNum.GCD

public section

namespace CFSG.StandardType

section Pairs

variable {β : Type*} [DecidableEq β]

private lemma bfChain_swap_eq_swap {a b c d : β} (hab : a ≠ b)
    (h : Equiv.swap a b = Equiv.swap c d) :
    (a = c ∧ b = d) ∨ (a = d ∧ b = c) := by
  have hb : Equiv.swap c d a = b := by rw [← h, Equiv.swap_apply_left]
  have ha : Equiv.swap c d b = a := by rw [← h, Equiv.swap_apply_right]
  by_cases hca : c = a
  · left
    refine ⟨hca.symm, ?_⟩
    rw [← hb, hca, Equiv.swap_apply_left]
  · right
    have hda : a = d := by
      have hne : Equiv.swap c d a ≠ a := by rw [hb]; exact hab.symm
      rcases (Equiv.swap_apply_ne_self_iff.mp hne) with ⟨_, h | h⟩
      · exact absurd h.symm hca
      · exact h
    refine ⟨hda, ?_⟩
    rw [← hb, hda, Equiv.swap_apply_right]

private lemma bfChain_swap_apply_eq {c d u v : β} (huv : u ≠ v)
    (h : Equiv.swap c d u = v) : Equiv.swap c d = Equiv.swap u v := by
  by_cases hcu : u = c
  · have hdv : d = v := by rw [← h, hcu, Equiv.swap_apply_left]
    rw [hcu, hdv]
  · have hud : u = d := by
      by_contra hud
      rw [Equiv.swap_apply_of_ne_of_ne hcu hud] at h
      exact huv h
    have hvc : v = c := by rw [← h, hud, Equiv.swap_apply_right]
    rw [← hud, hvc]
    exact Equiv.swap_comm c u

private lemma bfChain_swap_apply_eq_self {v z x : β} (hzv : z ≠ v)
    (h : Equiv.swap v z x = x) : x ≠ v ∧ x ≠ z := by
  constructor
  · intro hxv
    rw [hxv, Equiv.swap_apply_left] at h
    exact hzv h
  · intro hxz
    rw [hxz, Equiv.swap_apply_right] at h
    exact hzv h.symm

private lemma bfChain_braid_symm {G : Type*} [Group G] {a b : G}
    (ha : a * a = 1) (hb : b * b = 1) (h : (a * b) ^ 3 = 1) : (b * a) ^ 3 = 1 := by
  have hba : b * a = (a * b)⁻¹ := by
    rw [mul_inv_rev, inv_eq_of_mul_eq_one_right ha, inv_eq_of_mul_eq_one_right hb]
  rw [hba, inv_pow, h, inv_one]

theorem swap_fix_of_commute {u v : β} (huv : u ≠ v) {s : Equiv.Perm β} (hs : s.IsSwap)
    (hne : s ≠ Equiv.swap u v) (hc : s * Equiv.swap u v = Equiv.swap u v * s) :
    s u = u ∧ s v = v := by
  have hswap : Equiv.swap (s u) (s v) = Equiv.swap u v := by
    rw [Equiv.swap_apply_apply]
    rw [hc, mul_assoc, mul_inv_cancel, mul_one]
  rcases bfChain_swap_eq_swap (s.injective.ne huv) hswap with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact ⟨h1, h2⟩
  · exfalso
    rcases hs with ⟨p, q, hpq, rfl⟩
    exact hne (bfChain_swap_apply_eq huv h1)

theorem swap_share_of_braid {u v : β} (huv : u ≠ v) {s : Equiv.Perm β} (hs : s.IsSwap)
    (hne : s ≠ Equiv.swap u v) (h3 : (s * Equiv.swap u v) ^ 3 = 1) :
    ∃ z, z ≠ u ∧ z ≠ v ∧ (s = Equiv.swap u z ∨ s = Equiv.swap v z) := by
  rcases hs with ⟨c, d, hcd, rfl⟩
  by_cases hcu : c = u
  · refine ⟨d, ?_, ?_, Or.inl ?_⟩
    · intro hdu; exact hcd (hcu.trans hdu.symm)
    · intro hdv; exact hne (by rw [hcu, hdv])
    · rw [hcu]
  · by_cases hdu : d = u
    · refine ⟨c, ?_, ?_, Or.inl ?_⟩
      · exact hcu
      · intro hcv; exact hne (by rw [hcv, hdu, Equiv.swap_comm])
      · rw [hdu, Equiv.swap_comm]
    · by_cases hcv : c = v
      · refine ⟨d, ?_, ?_, Or.inr ?_⟩
        · exact hdu
        · intro hdv; exact hcd (hcv.trans hdv.symm)
        · rw [hcv]
      · by_cases hdv : d = v
        · refine ⟨c, ?_, ?_, Or.inr ?_⟩
          · exact hcu
          · exact hcv
          · rw [hdv, Equiv.swap_comm]
        · exfalso
          have hdisj : Equiv.Perm.Disjoint (Equiv.swap c d) (Equiv.swap u v) := by
            intro x
            by_cases hxc : x = c
            · right; rw [hxc]; exact Equiv.swap_apply_of_ne_of_ne hcu hcv
            · by_cases hxd : x = d
              · right; rw [hxd]; exact Equiv.swap_apply_of_ne_of_ne hdu hdv
              · left; exact Equiv.swap_apply_of_ne_of_ne hxc hxd
          have hcomm : Commute (Equiv.swap c d) (Equiv.swap u v) :=
            Equiv.Perm.Disjoint.commute hdisj
          have hs3 : Equiv.swap c d ^ 3 = Equiv.swap c d := by
            rw [pow_three, Equiv.swap_mul_self, mul_one]
          have ht3 : Equiv.swap u v ^ 3 = Equiv.swap u v := by
            rw [pow_three, Equiv.swap_mul_self, mul_one]
          have hmul : Equiv.swap c d * Equiv.swap u v = 1 := by
            have h := h3
            rw [hcomm.mul_pow, hs3, ht3] at h
            exact h
          exact hne (by
            have := eq_inv_of_mul_eq_one_left hmul
            simpa using this)

private lemma bfChain_not_mem_of_commute {p q v z : β} (hpq : p ≠ q) (hzv : z ≠ v)
    (hσ : Equiv.swap v z ≠ Equiv.swap p q)
    (hc : Equiv.swap v z * Equiv.swap p q = Equiv.swap p q * Equiv.swap v z) :
    z ≠ p ∧ z ≠ q := by
  have hswap : (Equiv.swap v z).IsSwap := ⟨v, z, hzv.symm, rfl⟩
  have hfix := swap_fix_of_commute hpq hswap hσ hc
  have hp := bfChain_swap_apply_eq_self hzv hfix.1
  have hq := bfChain_swap_apply_eq_self hzv hfix.2
  exact ⟨hp.2.symm, hq.2.symm⟩

end Pairs

section Chain

variable {β : Type*} [DecidableEq β]

theorem chain_labels_two {s₀ s₁ : Equiv.Perm β} (h₀ : s₀.IsSwap) (h₁ : s₁.IsSwap)
    (hne : s₀ ≠ s₁) (h3 : (s₀ * s₁) ^ 3 = 1) :
    ∃ a b c : β, a ≠ b ∧ a ≠ c ∧ b ≠ c ∧ s₀ = Equiv.swap a b ∧ s₁ = Equiv.swap b c := by
  obtain ⟨c, d, hcd, rfl⟩ := h₀
  have h3' : (s₁ * Equiv.swap c d) ^ 3 = 1 := by
    have hσ : s₁ * s₁ = 1 := by
      obtain ⟨p, q, hpq, rfl⟩ := h₁
      exact Equiv.swap_mul_self p q
    exact bfChain_braid_symm (Equiv.swap_mul_self c d) hσ h3
  obtain ⟨z, hzc, hzd, hz | hz⟩ :=
    swap_share_of_braid hcd h₁ (Ne.symm hne) h3'
  · exact ⟨d, c, z, hcd.symm, hzd.symm, hzc.symm, Equiv.swap_comm c d, hz⟩
  · exact ⟨c, d, z, hcd, hzc.symm, hzd.symm, rfl, hz⟩

theorem chain_labels (s : ℕ → Equiv.Perm β) (N : ℕ) (hN : 2 ≤ N)
    (hsw : ∀ c, c < N → (s c).IsSwap) (hne : ∀ c d, c < d → d < N → s c ≠ s d)
    (hbr : ∀ c, c + 1 < N → (s c * s (c + 1)) ^ 3 = 1)
    (hcomm : ∀ c d, c + 2 ≤ d → d < N → s c * s d = s d * s c) :
    ∃ w : ℕ → β, (∀ c d, c ≤ N → d ≤ N → w c = w d → c = d) ∧
      ∀ c, c < N → s c = Equiv.swap (w c) (w (c + 1)) := by
  suffices H : ∀ N : ℕ, 2 ≤ N → ∀ (s : ℕ → Equiv.Perm β)
      (hsw : ∀ c, c < N → (s c).IsSwap)
      (hne : ∀ c d, c < d → d < N → s c ≠ s d)
      (hbr : ∀ c, c + 1 < N → (s c * s (c + 1)) ^ 3 = 1)
      (hcomm : ∀ c d, c + 2 ≤ d → d < N → s c * s d = s d * s c),
      ∃ w : ℕ → β, (∀ c d, c ≤ N → d ≤ N → w c = w d → c = d) ∧
        ∀ c, c < N → s c = Equiv.swap (w c) (w (c + 1)) by
    exact H N hN s hsw hne hbr hcomm
  intro N hN
  refine Nat.le_induction (m := 2) ?base ?step N hN
  · intro s hsw hne hbr hcomm
    obtain ⟨a, b, c, hab, hac, hbc, hs0, hs1⟩ :=
      chain_labels_two (hsw 0 (by omega)) (hsw 1 (by omega))
        (hne 0 1 (by omega) (by omega)) (hbr 0 (by omega))
    refine ⟨fun k => if k = 0 then a else if k = 1 then b else c, ?_, ?_⟩
    · intro c' d' hc hd h
      have hc0 : c' = 0 ∨ c' = 1 ∨ c' = 2 := by omega
      have hd0 : d' = 0 ∨ d' = 1 ∨ d' = 2 := by omega
      rcases hc0 with rfl | rfl | rfl <;> rcases hd0 with rfl | rfl | rfl <;> simp_all
    · intro c' hc
      have hc0 : c' = 0 ∨ c' = 1 := by omega
      rcases hc0 with rfl | rfl <;> simp [hs0, hs1]
  · intro n hn ih s hsw hne hbr hcomm
    obtain ⟨w, hinj, hsw_w⟩ :=
      ih s (fun c hc => hsw c (by omega))
         (fun c d hcd hd => hne c d hcd (by omega))
         (fun c hc => hbr c (by omega))
         (fun c d hcd hd => hcomm c d hcd (by omega))
    have huv : w (n - 1) ≠ w n := by
      intro h
      have := hinj (n - 1) n (by omega) (by omega) h
      omega
    have hs_prev : s (n - 1) = Equiv.swap (w (n - 1)) (w n) := by
      have h := hsw_w (n - 1) (by omega)
      simpa [Nat.sub_add_cancel (by omega : 1 ≤ n)] using h
    have hσsw : (s n).IsSwap := hsw n (by omega)
    have hσ_inv : s n * s n = 1 := by
      obtain ⟨p, q, hpq, hpq'⟩ := hσsw
      rw [hpq']; exact Equiv.swap_mul_self p q
    have h3a : (Equiv.swap (w (n - 1)) (w n) * s n) ^ 3 = 1 := by
      have h := hbr (n - 1) (by omega)
      rw [Nat.sub_add_cancel (by omega : 1 ≤ n), hs_prev] at h
      exact h
    have h3 : (s n * Equiv.swap (w (n - 1)) (w n)) ^ 3 = 1 :=
      bfChain_braid_symm (Equiv.swap_mul_self (w (n - 1)) (w n)) hσ_inv h3a
    have hne_prev : s n ≠ Equiv.swap (w (n - 1)) (w n) := by
      rw [← hs_prev]
      exact (hne (n - 1) n (by omega) (by omega)).symm
    obtain ⟨z, hzu, hzv, hzu' | hzv'⟩ :=
      swap_share_of_braid huv hσsw hne_prev h3
    · exfalso
      have hp_ne_u : w (n - 2) ≠ w (n - 1) := by
        intro h
        have := hinj (n - 2) (n - 1) (by omega) (by omega) h
        omega
      have hs_n2 : s (n - 2) = Equiv.swap (w (n - 2)) (w (n - 1)) := by
        have h := hsw_w (n - 2) (by omega)
        have hstep : n - 2 + 1 = n - 1 := by omega
        rwa [hstep] at h
      have hcomm_n2 : s (n - 2) * s n = s n * s (n - 2) :=
        hcomm (n - 2) n (by omega) (by omega)
      have hne_n2 : s n ≠ Equiv.swap (w (n - 2)) (w (n - 1)) := by
        rw [← hs_n2]
        exact (hne (n - 2) n (by omega) (by omega)).symm
      have hcomm_n2' : s n * Equiv.swap (w (n - 2)) (w (n - 1))
          = Equiv.swap (w (n - 2)) (w (n - 1)) * s n := by
        rw [← hs_n2]; exact hcomm_n2.symm
      have hfix := swap_fix_of_commute hp_ne_u hσsw hne_n2 hcomm_n2'
      have hz_eq : z = w (n - 1) := by
        have h := hfix.2
        rw [hzu'] at h
        simpa using h
      exact hzu hz_eq
    · have hz_step : ∀ c, c + 2 ≤ n → z ≠ w c ∧ z ≠ w (c + 1) := by
        intro c hc
        have hc_lt : c < n := by omega
        have hw := hsw_w c hc_lt
        have hcomm_c : s c * s n = s n * s c := hcomm c n hc (by omega)
        have hne_c : s n ≠ s c := (hne c n (by omega) (by omega)).symm
        have hσne : Equiv.swap (w n) z ≠ Equiv.swap (w c) (w (c + 1)) := by
          rw [← hzv', ← hw]
          exact hne_c
        have hcomm_c' : Equiv.swap (w n) z * Equiv.swap (w c) (w (c + 1))
            = Equiv.swap (w c) (w (c + 1)) * Equiv.swap (w n) z := by
          rw [← hzv', ← hw]
          exact hcomm_c.symm
        have hpq : w c ≠ w (c + 1) := by
          intro h
          have := hinj c (c + 1) (by omega) (by omega) h
          omega
        exact bfChain_not_mem_of_commute hpq hzv hσne hcomm_c'
      have hz_w : ∀ k, k ≤ n → z ≠ w k := by
        intro k hk
        rcases lt_or_eq_of_le hk with hklt | hkeq
        · rcases k with _ | k
          · exact (hz_step 0 (by omega)).1
          · have h2 : k + 2 ≤ n := by omega
            exact (hz_step k h2).2
        · rw [hkeq]; exact hzv
      let w' : ℕ → β := fun k => if k ≤ n then w k else z
      have w'_le : ∀ k, k ≤ n → w' k = w k := by intro k hk; simp [w', hk]
      have w'_n : w' n = w n := by simp [w']
      have w'_succ : w' (n + 1) = z := by
        simp only [w', if_neg (by omega : ¬ n + 1 ≤ n)]
      refine ⟨w', ?_, ?_⟩
      · intro c d hc hd h
        by_cases hc' : c ≤ n
        · by_cases hd' : d ≤ n
          · rw [w'_le c hc', w'_le d hd'] at h
            exact hinj c d hc' hd' h
          · have hd_eq : d = n + 1 := by omega
            rw [w'_le c hc', hd_eq, w'_succ] at h
            exact absurd h.symm (hz_w c hc')
        · have hc_eq : c = n + 1 := by omega
          rw [hc_eq] at h ⊢
          by_cases hd' : d ≤ n
          · rw [w'_succ, w'_le d hd'] at h
            exact absurd h (hz_w d hd')
          · omega
      · intro c hc
        by_cases hcn : c < n
        · rw [hsw_w c hcn, w'_le c (by omega), w'_le (c + 1) (by omega)]
        · have hc_eq : c = n := by omega
          rw [hc_eq, w'_n, w'_succ]
          exact hzv'

end Chain

end CFSG.StandardType
