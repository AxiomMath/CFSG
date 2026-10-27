module

public import CFSG.Quasithin.EmptyFaithful.S146zNFinU
public import CFSG.Quasithin.EmptyFaithful.S146zNFinJ
public import CFSG.Quasithin.EmptyFaithful.S146zNFinS

public section

namespace CFSG.Quasithin.A6Fin

open Equiv Equiv.Perm CFSG.Quasithin CFSG.Quasithin.A6Mod

variable {W : Type} [CommGroup W] [Finite W] {ρ : A6 →* MulAut W}

theorem Setup.cent_three_of_odd (h : Setup ρ) (n : MulAut W)
    (hn : ∀ g : A6, ∃ k : A6, ρ k = n * ρ g * n⁻¹) (hn2 : n * n = 1) (hnL : ¬ ∃ k : A6, ρ k = n) :
    ∃ g : A6, g ^ 3 = 1 ∧ g ≠ 1 ∧ n * ρ g * n⁻¹ = ρ g := by
  obtain ⟨σ, hσ⟩ := h.kap_conj n hn
  have hodd := h.sign_odd n hn σ hσ hnL
  have hkk : ∀ g : A6, kap h n hn (kap h n hn g) = g := by
    intro g
    apply h.inj
    rw [kap_spec h n hn, kap_spec h n hn]
    calc n * (n * ρ g * n⁻¹) * n⁻¹ = (n * n) * ρ g * (n * n)⁻¹ := by group
      _ = ρ g := by rw [hn2]; group
  have hs2 : σ * σ = 1 := by
    have hcomm : ∀ g : A6, σ * σ * g.1 = g.1 * (σ * σ) := by
      intro g
      have e := congrArg Subtype.val (hkk g)
      have e1 : ((kap h n hn (kap h n hn g) : A6) : Perm (Fin 6)) = σ * (σ * g.1 * σ⁻¹) * σ⁻¹ := by
        rw [hσ, hσ]
      calc σ * σ * g.1 = (σ * (σ * g.1 * σ⁻¹) * σ⁻¹) * (σ * σ) := by group
        _ = g.1 * (σ * σ) := by rw [← e1, e]
    exact cent_x0y0 _ (hcomm x0A6) (hcomm y0A6)
  obtain ⟨g₀, hg₀s, hg₀3, hg₀1, hg₀c⟩ := odd_invol_cent3 σ hs2 hodd
  refine ⟨⟨g₀, mem_alternatingGroup.mpr hg₀s⟩, ?_, ?_, ?_⟩
  · apply Subtype.ext
    simpa [pow_succ, mul_assoc] using hg₀3
  · intro e
    exact hg₀1 (congrArg Subtype.val e)
  · have hk : kap h n hn ⟨g₀, mem_alternatingGroup.mpr hg₀s⟩ = ⟨g₀, mem_alternatingGroup.mpr hg₀s⟩ := by
      apply Subtype.ext
      rw [hσ]
      show σ * g₀ * σ⁻¹ = g₀
      rw [← hg₀c]
      group
    rw [← kap_spec h n hn, hk]


theorem Setup.fix_data (h : Setup ρ) (γ : MulAut W) (hγ2 : γ * γ = 1) (hγL : ¬ ∃ k : A6, ρ k = γ) :
    4 ≤ Nat.card (fixSub γ) ∧ Nat.card (fixSub γ) ≠ 16 ∧
      Nat.card (fixSub γ) * 2 ^ A6Rank γ = 16 := by
  refine ⟨?_, ?_, rank_spec h.card γ⟩
  · have := le_card_fixSub_sq h.sq γ hγ2
    rw [h.card] at this
    by_contra hcon
    push Not at hcon
    interval_cases hc : Nat.card (fixSub γ) <;> omega
  · intro h16
    apply hγL
    refine ⟨1, ?_⟩
    have htop : fixSub γ = ⊤ := Subgroup.eq_top_of_card_eq _ (by rw [h16, h.card])
    rw [map_one]
    ext w
    have : w ∈ fixSub γ := by rw [htop]; trivial
    exact (mem_fixSub.mp this).symm

theorem rank_cases {c r : ℕ} (hrs : c * 2 ^ r = 16) (h4 : 4 ≤ c) (h16 : c ≠ 16) :
    (c = 8 ∧ r = 1) ∨ (c = 4 ∧ r = 2) := by
  have hle : 2 ^ r ≤ 16 := Nat.le_of_dvd (by norm_num) (Dvd.intro_left c hrs)
  have hr : r ≤ 4 := by
    by_contra hcon
    push Not at hcon
    have : 2 ^ 5 ≤ 2 ^ r := Nat.pow_le_pow_right (by norm_num) hcon
    omega
  interval_cases r <;> norm_num at hrs ⊢ <;> omega

theorem Setup.rank_sum (h : Setup ρ) (β : MulAut A6)
    (hβ : ∃ x : A6, x ^ 3 = 1 ∧ x ≠ 1 ∧ ∀ l : A6, l * x * l⁻¹ ≠ β x)
    (n n' : MulAut W) (hn : ∀ g : A6, ∃ k : A6, ρ k = n * ρ g * n⁻¹)
    (hn' : ∀ g : A6, ∃ k : A6, ρ k = n' * ρ g * n'⁻¹)
    (hn2 : n * n = 1) (hn'2 : n' * n' = 1) (hnL : ¬ ∃ k : A6, ρ k = n) (hn'L : ¬ ∃ k : A6, ρ k = n')
    (hrel : ∀ g k : A6, n' * ρ g * n'⁻¹ = ρ k → n * ρ (β g) * n⁻¹ = ρ (β k)) :
    3 ≤ A6Rank n + A6Rank n' := by
  obtain ⟨hc4, hc16, hrs⟩ := h.fix_data n hn2 hnL
  obtain ⟨hc4', hc16', hrs'⟩ := h.fix_data n' hn'2 hn'L
  obtain ⟨g, hg3, hg1, hgn⟩ := h.cent_three_of_odd n hn hn2 hnL
  set g' := β.symm g with hg'
  have hg'3 : g' ^ 3 = 1 := by
    rw [hg', ← map_pow β.symm, hg3, map_one]
  have hg'1 : g' ≠ 1 := fun e => hg1 (by rw [hg'] at e; simpa using congrArg β e)
  have hβg' : β g' = g := by simp [hg']
  have hn'g' : n' * ρ g' * n'⁻¹ = ρ g' := by
    have h1 := hrel g' (kap h n' hn' g') (kap_spec h n' hn' g').symm
    rw [hβg', hgn] at h1
    have h2 : kap h n' hn' g' = g' := by
      apply β.injective
      rw [hβg']
      exact (h.inj h1).symm
    rw [← kap_spec h n' hn' g', h2]
  have hfc := fc_val16 h.nontrivial h.card hg1 hg3
  have hfc' := fc_val16 h.nontrivial h.card hg'1 hg'3
  have hfuse := h.fc_fuse β hβ g' hg'3 hg'1
  rw [hβg'] at hfuse
  have hr' := rank_cases hrs' hc4' hc16'
  rcases rank_cases hrs hc4 hc16 with ⟨hc8, hr1⟩ | ⟨hc4n, hr2⟩
  · rcases hr' with ⟨hc8', hr1'⟩ | ⟨hc4n', hr2'⟩
    · exfalso
      have hcomm : ρ g * n = n * ρ g := by
        rw [mul_inv_eq_iff_eq_mul] at hgn
        exact hgn.symm
      have hg_fc4 : fc ρ g = 4 := by
        rcases hfc with h1 | h4
        · exfalso
          have := card_fixSub_modEq_three ρ hg3 h1 n hcomm
          rw [hc8] at this
          unfold Nat.ModEq at this
          omega
        · exact h4
      have hg'_fc1 : fc ρ g' = 1 := by
        rcases hfc' with h1 | h4
        · exact h1
        · exfalso; exact hfuse (by rw [hg_fc4, h4])
      have hcomm' : ρ g' * n' = n' * ρ g' := by
        rw [mul_inv_eq_iff_eq_mul] at hn'g'
        exact hn'g'.symm
      have hmod := card_fixSub_modEq_three ρ hg'3 hg'_fc1 n' hcomm'
      rw [hc8'] at hmod
      unfold Nat.ModEq at hmod
      omega
    · omega
  · rcases hr' with ⟨_, hr1'⟩ | ⟨_, hr2'⟩ <;> omega

end CFSG.Quasithin.A6Fin
