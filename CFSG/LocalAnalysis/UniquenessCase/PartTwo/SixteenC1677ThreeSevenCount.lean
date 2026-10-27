module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1677ThreeTools
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightD3Kernel
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven10MBarFour

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

theorem s168e3_seven_eq_of_sq_dvd {q r : ℕ} (hq : q.Prime) (hq2 : q ≠ 2) (hr : r ≤ 5)
    (h : q ^ 2 ∣ 7 ^ (r + 1) * 3 * Nat.factorial (r + 1)) : q = 3 ∨ q = 7 := by
  have hq3 : 3 ≤ q := by
    by_contra hle
    have hlt : q < 3 := not_le.1 hle
    interval_cases q
    · exact Nat.not_prime_zero hq
    · exact Nat.not_prime_one hq
    · exact hq2 rfl
  have hdvd : q ∣ 7 ^ (r + 1) * 3 * Nat.factorial (r + 1) :=
    (dvd_pow_self q (n := 2) (by norm_num)).trans h
  have hqmem : q = 7 ∨ q = 3 ∨ q = 5 := by
    rcases hq.dvd_mul.1 hdvd with h1 | h1
    · rcases hq.dvd_mul.1 h1 with h2 | h2
      · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 7)).1
          (hq.dvd_of_dvd_pow h2))
      · exact Or.inr (Or.inl ((Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 3)).1 h2))
    · have hle : q ≤ r + 1 := (hq.dvd_factorial).1 h1
      have hq6 : q ≤ 6 := by omega
      interval_cases q
      · exact Or.inr (Or.inl rfl)
      · exact absurd hq (by decide)
      · exact Or.inr (Or.inr rfl)
      · exact absurd hq (by decide)
  rcases hqmem with rfl | rfl | rfl
  · exact Or.inr rfl
  · exact Or.inl rfl
  · exfalso
    interval_cases r <;> norm_num at h

variable {W : Type} [CommGroup W] [Finite W] {A L : Subgroup (MulAut W)} {r : ℕ}
  {Δ : Fin (r + 1) → Subgroup W} {σ : ↥A →* Equiv.Perm (Fin (r + 1))}

theorem s168e3_seven_two_lt_mParam (h : s16e_d3_Ctx A L r Δ σ) : 2 < E3.mParam A := by
  classical
  have hinv : ∀ φ ∈ A, orderOf φ = 2 → 3 ≤ rkIdx (fixV (Subgroup.zpowers φ)) := by
    intro φ hφA hφ
    by_contra hlt
    have hlt' : rkIdx (fixV (Subgroup.zpowers φ)) < 3 := not_le.1 hlt
    let g : ↥A := ⟨φ, hφA⟩
    have hg2 : g ^ 2 = 1 := by
      apply Subtype.ext
      show φ ^ 2 = 1
      rw [← hφ]
      exact pow_orderOf_eq_one φ
    have hσ2 : σ g ^ 2 = 1 := by rw [← map_pow, hg2, map_one]
    by_cases hσ1 : σ g = 1
    · have hker : φ ∈ s16e_d3_ker A Δ :=
        (s16e_d3_mem_ker_iff h.cfg).2 ⟨hφA, hσ1⟩
      have h2 : (2 : ℕ) ∣ Nat.card ↥(s16e_d3_ker A Δ) := by
        rw [← hφ, ← Subgroup.orderOf_mk φ hker]
        exact orderOf_dvd_natCard _
      have h2' : (2 : ℕ) ∣ 7 ^ (r + 1) * 3 :=
        h2.trans (s16e_d3_card_ker_dvd_seven_pow_mul_three h)
      rcases Nat.Prime.dvd_mul Nat.prime_two |>.1 h2' with h2'' | h2''
      · exact (by norm_num : ¬ (2 : ℕ) ∣ 7) (Nat.prime_two.dvd_of_dvd_pow h2'')
      · exact (by norm_num : ¬ (2 : ℕ) ∣ 3) h2''
    · have hex : ∃ i, σ g i ≠ i := by
        by_contra hcon
        push Not at hcon
        exact hσ1 (Equiv.ext hcon)
      obtain ⟨i, hi⟩ := hex
      let j : Fin (r + 1) := σ g i
      have hji : j ≠ i := hi
      have hij : i ≠ j := fun hh => hji hh.symm
      have hj : σ g j = i := by
        have h2 := congrArg (fun e : Equiv.Perm (Fin (r + 1)) => e i) hσ2
        simpa [j, pow_two, Equiv.Perm.mul_apply] using h2
      have hmap_i : (Δ i).map φ.toMonoidHom = Δ j := by
        have hh := h.cfg.map_eq g i
        simpa [g, j] using hh
      have hmap_j : (Δ j).map φ.toMonoidHom = Δ i := by
        have hh := h.cfg.map_eq g j
        rw [hj] at hh
        simpa [g] using hh
      have h3 := s16c1610_le_rkIdx_fixV_swap h.sq_eq_one
        (h.cfg.indep.pairwiseDisjoint hij) (h.cfg.rk_eq i) (h.cfg.rk_eq j) hmap_i hmap_j
      omega
  unfold E3.mParam
  split_ifs with hev
  · set S : Set ℕ :=
      {n : ℕ | ∃ t ∈ A, orderOf t = 2 ∧ n = rkIdx (fixV (Subgroup.zpowers t))} with hS
    have hne : S.Nonempty := by
      haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := ↥A) 2 (even_iff_two_dvd.1 hev)
      exact ⟨_, (x : MulAut W), x.2, by rw [Subgroup.orderOf_coe]; exact hx, rfl⟩
    obtain ⟨t, htA, ht2, hn⟩ := Nat.sInf_mem hne
    rw [hn]
    have := hinv t htA ht2
    omega
  · have h1 : rk ↥(Δ 0) ≤ rk ↥(⊤ : Subgroup W) := rk_mono le_top
    rw [rk_top, h.cfg.rk_eq 0] at h1
    omega

variable {G : Type} [Group G] [Finite G]

theorem s168e3_seven_eq_of_mem_sig {D : Data G} {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (c : S168e3Ctx D V₀ V L hV) {r : ℕ} {Δ : Fin (r + 1) → Subgroup (Vtil V₀ V hV)}
    {σ : ↥(Mbar D.M V₀ V hV) →* Equiv.Perm (Fin (r + 1))}
    (h : s16e_d3_Ctx (Mbar D.M V₀ V hV) (lBar V₀ V hV L) r Δ σ) {q : ℕ} (hq : q ∈ D.sig) :
    q = 3 ∨ q = 7 := by
  obtain ⟨hqp, hq2⟩ := D.sig_prime q hq
  obtain ⟨E, -, hEcard⟩ :=
    exists_isElemAbelian_subgroupOf_of_le_pRank (M := Mbar D.M V₀ V hV) hqp
      (c.two_le_pRank_mbar hq)
  have hdvd : q ^ 2 ∣ Nat.card ↥(Mbar D.M V₀ V hV) := by
    rw [← hEcard]
    exact Subgroup.card_subgroup_dvd_card E
  exact s168e3_seven_eq_of_sq_dvd hqp hq2 h.le_five
    (hdvd.trans (s16e_d3_card_dvd_seven_pow_mul_three_mul_factorial h))

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
