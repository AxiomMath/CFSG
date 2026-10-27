module

public import CFSG.Quasithin.Vol2.Asc94.TS39f

public section

namespace CFSG.Quasithin.A94

open CFSG.CGT.Timmesfeld75 CFSG.Open

variable {G : Type} [Group G] [Finite G] {z : G}

theorem Frame3.Δ_nonempty (F : Frame3 G z) (i : Fin 7) : (F.Δ i).Nonempty :=
  Set.nonempty_of_ncard_ne_zero (by rw [F.Δ_card i]; fin_cases i <;> simp)

theorem Frame3.Δ1_sub_Sz (F : Frame3 G z) (hU1 : ∀ u ∈ F.U, u ≠ 1 → InZG z u) :
    F.Δ 1 ⊆ F.Sz := by
  intro s hs
  rw [F.Δ1] at hs
  obtain ⟨h1, h2⟩ := hs
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at h2
  exact ⟨(Subgroup.mem_inf.1 h1).1, h2.1, hU1 _ (Subgroup.mem_inf.1 h1).2 h2.1⟩

theorem Frame3.Δ0_sub_Sz (F : Frame3 G z) : F.Δ 0 ⊆ F.Sz := by
  intro s hs
  rw [F.Δ0] at hs
  rw [Set.mem_singleton_iff.1 hs]
  exact ⟨F.z_mem_A, F.z_ne_one, 1, by simp⟩

theorem Frame3.not_Δ2_sub_Sz (F : Frame3 G z)
    (hU2 : ¬ ∀ u ∈ F.U2, u ≠ 1 → InZG z u) : ¬ F.Δ 2 ⊆ F.Sz := by
  intro hsub
  apply hU2
  obtain ⟨a, ha⟩ := F.Δ_nonempty 2
  obtain ⟨haU, ha1, haz⟩ := F.Δ2_sub a ha
  obtain ⟨-, -, g, hg⟩ := hsub ha
  intro u hu hu1
  by_cases huz : u = z
  · exact ⟨1, by simp [huz]⟩
  · obtain ⟨h, hh, huh⟩ := F.U2_trans a haU ha1 haz u hu hu1 huz
    exact ⟨g * h, by rw [huh, hg]; group⟩

theorem Frame3.not_Δ3_sub_Sz (F : Frame3 G z) : ¬ F.Δ 3 ⊆ F.Sz := by
  intro hsub
  obtain ⟨a, ha⟩ := F.Δ_nonempty 3
  obtain ⟨-, -, g, hg⟩ := hsub ha
  exact s39_4 F.toFrame1 a (F.Δ3_sub a ha) g hg.symm

theorem Frame3.dich (F : Frame3 G z) (i : Fin 7) : F.Δ i ⊆ F.Sz ∨ Disjoint (F.Δ i) F.Sz := by
  by_cases h : ∃ a, a ∈ F.Δ i ∧ a ∈ F.Sz
  · left
    obtain ⟨a, haΔ, haS⟩ := h
    intro b hb
    obtain ⟨x, hx, rfl⟩ := F.Δ_trans i a haΔ b hb
    exact F.conj_mem_Sz haS hx.2
  · right
    rw [Set.disjoint_left]
    intro a ha haS
    exact h ⟨a, ha, haS⟩

private theorem hcong_of (p : ℕ) (key : ∀ c ∈ Nat.divisors 64, c % p = 64 % p → c = 64) :
    ∀ c : ℕ, c ∣ 64 → Nat.ModEq p 64 c → c = 64 := by
  intro c hc hmod
  exact key c (Nat.mem_divisors.2 ⟨hc, by norm_num⟩) hmod.symm

theorem s39_7 (F : Frame3 G z) (hU1 : ∀ u ∈ F.U, u ≠ 1 → InZG z u)
    (hU2 : ¬ ∀ u ∈ F.U2, u ≠ 1 → InZG z u) :
    Subgroup.normalizer (F.A : Set G) ≤ Subgroup.normalizer (F.U : Set G) ∧
      (∀ a ∈ F.A, a ≠ 1 → InZG z a → a ∈ F.U) ∧
      Subgroup.normalizer (F.U : Set G) ≠ Cz z := by
  classical
  have hdich := F.dich
  have h0 := F.Δ0_sub_Sz
  have h1 := F.Δ1_sub_Sz hU1
  have h2 := F.not_Δ2_sub_Sz hU2
  have h3 := F.not_Δ3_sub_Sz
  have hsum := F.ncard_Sz_eq_sum hdich
  rw [Fin.sum_univ_seven, if_pos h0, if_pos h1, if_neg h2, if_neg h3] at hsum
  have c0 : (F.Δ 0).ncard = 1 := by simpa using F.Δ_card 0
  have c1 : (F.Δ 1).ncard = 6 := by simpa using F.Δ_card 1
  have c4 : (F.Δ 4).ncard = 12 := by simpa using F.Δ_card 4
  have c5 : (F.Δ 5).ncard = 12 := by simpa using F.Δ_card 5
  have c6 : (F.Δ 6).ncard = 24 := by simpa using F.Δ_card 6
  rw [c0, c1] at hsum
  have hexcl : ∀ n : ℕ, F.Sz.ncard = n → (∃ j : Fin 7, 4 ≤ j.val ∧ F.Δ j ⊆ F.Sz) →
      (n = 19 ∨ n = 31 ∨ n = 43 ∨ n = 55) → False := by
    intro n hn hj hcases
    rcases hcases with rfl | rfl | rfl | rfl
    · haveI : Fact (Nat.Prime 19) := ⟨by norm_num⟩
      refine Frame2.not_prime_dvd_card_normalizer F.toFrame2 19 (by norm_num)
        (hcong_of 19 (by decide)) ?_
      rw [Frame2.card_normalizer_A F.toFrame2, hn]
      exact dvd_mul_right 19 _
    · exact F.false_of_card_31 hU1 hn hj
    · haveI : Fact (Nat.Prime 43) := ⟨by norm_num⟩
      refine Frame2.not_prime_dvd_card_normalizer F.toFrame2 43 (by norm_num)
        (hcong_of 43 (by decide)) ?_
      rw [Frame2.card_normalizer_A F.toFrame2, hn]
      exact dvd_mul_right 43 _
    · haveI : Fact (Nat.Prime 11) := ⟨by norm_num⟩
      refine Frame2.not_prime_dvd_card_normalizer F.toFrame2 11 (by norm_num)
        (hcong_of 11 (by decide)) ?_
      rw [Frame2.card_normalizer_A F.toFrame2, hn]
      exact Dvd.dvd.mul_right (by norm_num : 11 ∣ 55) _
  by_cases hall : ¬ F.Δ 4 ⊆ F.Sz ∧ ¬ F.Δ 5 ⊆ F.Sz ∧ ¬ F.Δ 6 ⊆ F.Sz
  ·
    obtain ⟨h4, h5, h6⟩ := hall
    have hdisj : ∀ i : Fin 7, ¬ F.Δ i ⊆ F.Sz → Disjoint (F.Δ i) F.Sz := fun i hi =>
      (hdich i).resolve_left hi
    have hSz : ∀ a : G, a ∈ F.Sz → a ∈ F.A ⊓ F.U := by
      intro a ha
      have haU : a ∈ ⋃ i, F.Δ i := by
        rw [F.Δ_union]
        exact ⟨ha.1, ha.2.1⟩
      obtain ⟨i, hi⟩ := Set.mem_iUnion.1 haU
      have hfin7 : ∀ i : Fin 7, i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 := by
        decide
      rcases hfin7 i with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · rw [F.Δ0] at hi
        rw [Set.mem_singleton_iff.1 hi]
        exact ⟨F.z_mem_A, F.toFrame1.toFrame0.z_mem_U⟩
      · rw [F.Δ1] at hi
        exact hi.1
      · exact absurd ha (Set.disjoint_left.1 (hdisj 2 h2) hi)
      · exact absurd ha (Set.disjoint_left.1 (hdisj 3 h3) hi)
      · exact absurd ha (Set.disjoint_left.1 (hdisj 4 h4) hi)
      · exact absurd ha (Set.disjoint_left.1 (hdisj 5 h5) hi)
      · exact absurd ha (Set.disjoint_left.1 (hdisj 6 h6) hi)
    have hSz' : ∀ a : G, a ∈ F.A ⊓ F.U → a ≠ 1 → a ∈ F.Sz := fun a ha ha1 =>
      ⟨(Subgroup.mem_inf.1 ha).1, ha1, hU1 a (Subgroup.mem_inf.1 ha).2 ha1⟩
    have hL : Subgroup.normalizer (F.A : Set G) ≤ Subgroup.normalizer ((F.A ⊓ F.U : Subgroup G) : Set G) := by
      intro l hl
      have hfwd : ∀ l ∈ Subgroup.normalizer (F.A : Set G), ∀ d ∈ F.A ⊓ F.U, l⁻¹ * d * l ∈ F.A ⊓ F.U := by
        intro l hl d hd
        by_cases hd1 : d = 1
        · rw [hd1]
          simpa using (F.A ⊓ F.U).one_mem
        · exact hSz _ (F.conj_mem_Sz (hSz' d hd hd1) hl)
      rw [Subgroup.mem_normalizer_iff]
      intro d
      constructor
      · intro hd
        have := hfwd l⁻¹ (Subgroup.inv_mem _ hl) d hd
        simpa using this
      · intro hd
        have := hfwd l hl _ hd
        simpa [mul_assoc] using this
    have hLU : Subgroup.normalizer (F.A : Set G) ≤ Subgroup.normalizer (F.U : Set G) := by
      intro l hl
      have := hL hl
      rw [s39_6_4 F.toFrame2] at this
      exact this.2
    refine ⟨hLU, fun a ha ha1 haz => (Subgroup.mem_inf.1 (hSz a ⟨ha, ha1, haz⟩)).2, ?_⟩
    intro hH
    obtain ⟨a, ha⟩ := F.Δ_nonempty 1
    have haS := h1 ha
    have hane : a ≠ z := by
      rw [F.Δ1] at ha
      have := ha.2
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at this
      exact this.2
    obtain ⟨g, hg⟩ := haS.2.2
    obtain ⟨n, hn, hna⟩ := s39_6_3 F.toFrame2 F.z_mem_A haS.1 hg.symm
    have hnH : n ∈ Cz z := by rw [← hH]; exact hLU hn
    have hnz : n⁻¹ * z * n = z := by
      have := Subgroup.mem_centralizer_singleton_iff.1 hnH
      calc n⁻¹ * z * n = n⁻¹ * (z * n) := by group
        _ = n⁻¹ * (n * z) := by rw [← this]
        _ = z := by group
    exact hane (by rw [← hna, hnz])
  · exfalso
    have hj : ∃ j : Fin 7, 4 ≤ j.val ∧ F.Δ j ⊆ F.Sz := by
      by_contra hcon
      push Not at hcon
      exact hall ⟨hcon 4 (by decide), hcon 5 (by decide), hcon 6 (by decide)⟩
    apply hexcl _ rfl hj
    by_cases h4 : F.Δ 4 ⊆ F.Sz <;> by_cases h5 : F.Δ 5 ⊆ F.Sz <;>
      by_cases h6 : F.Δ 6 ⊆ F.Sz <;> simp [h4, h5, h6, c4, c5, c6] at hsum <;>
      first | omega | exact absurd ⟨h4, h5, h6⟩ hall

end CFSG.Quasithin.A94
