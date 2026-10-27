module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec6P62Dih

public section

namespace CFSG.Quasithin.Fan86

open SimpleGraph CFSG.Quasithin.F6.GoldAmL3T

variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V}

namespace P517

theorem no_three_cycle (F : FanTree Γ G) {α : V} (hα : valence Γ α = 5) {t : G}
    (ht : t ∈ MulAction.stabilizer G α) {a b c : V} (ha : Γ.Adj α a) (hb : Γ.Adj α b)
    (hac : a ≠ c) (hab : a ≠ b) (hta : t • a = c) (htc : t • c = b) (htb : t • b = a)
    (hc : Γ.Adj α c) : False := by
  have hfin : Finite (Γ.neighborSet α) := F.finite_neighborSet α
  let _ : Fintype (Γ.neighborSet α) := Fintype.ofFinite _
  classical
  have h3 : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set σ := F.localHom α ⟨t, ht⟩ with hσ
  have hσa : σ ⟨a, ha⟩ = ⟨c, hc⟩ := Subtype.ext hta
  have hσc : σ ⟨c, hc⟩ = ⟨b, hb⟩ := Subtype.ext htc
  have hσb : σ ⟨b, hb⟩ = ⟨a, ha⟩ := Subtype.ext htb
  have hcube : ∀ p : Γ.neighborSet α, p = ⟨a, ha⟩ ∨ p = ⟨b, hb⟩ → (σ ^ 3) p = p := by
    rintro p (rfl | rfl)
    · simp [pow_succ, Equiv.Perm.mul_apply, hσa, hσc, hσb]
    · simp [pow_succ, Equiv.Perm.mul_apply, hσa, hσc, hσb]
  have hσ3 : σ ^ 3 = 1 := by
    refine F.localHom_frobenius α (σ ^ 3) ⟨⟨t, ht⟩ ^ 3, by rw [map_pow]⟩ ⟨a, ha⟩ ⟨b, hb⟩
      (fun e => hab (congrArg Subtype.val e)) (hcube _ (Or.inl rfl)) (hcube _ (Or.inr rfl))
  have hmod := Equiv.Perm.card_compl_support_modEq (p := 3) (n := 1) (σ := σ) (by simpa using hσ3)
  have hcard : Fintype.card (Γ.neighborSet α) = 5 := by
    rw [Fintype.card_eq_nat_card]
    exact hα
  rw [hcard] at hmod
  have hge : 1 < σ.supportᶜ.card := by
    unfold Nat.ModEq at hmod
    omega
  obtain ⟨p, hp, q, hq, hpq⟩ := Finset.one_lt_card.1 hge
  have hp' : σ p = p := by simpa using hp
  have hq' : σ q = q := by simpa using hq
  have h1 : σ = 1 := F.localHom_frobenius α σ ⟨⟨t, ht⟩, rfl⟩ p q hpq hp' hq'
  have := hσa
  rw [h1] at this
  exact hac (congrArg Subtype.val this)

theorem swap_third (F : FanTree Γ G) {α ν₁ ν₂ ν₃ : V} (hα : valence Γ α = 5)
    (h1 : Γ.Adj α ν₁) (h2 : Γ.Adj α ν₂) (h3 : Γ.Adj α ν₃) (h12 : ν₁ ≠ ν₂) (h13 : ν₁ ≠ ν₃) :
    (∃ s ∈ MulAction.stabilizer G α, s • ν₁ = ν₂ ∧ s • ν₂ = ν₁ ∧ s • ν₃ ≠ ν₃) ∨
      ∃ s ∈ MulAction.stabilizer G α, s • ν₁ = ν₃ ∧ s • ν₃ = ν₁ ∧ s • ν₂ ≠ ν₂ := by
  obtain ⟨s₁, hs₁, a₁, a₂, -⟩ := P62.exists_swap F hα h1 h2
  obtain ⟨s₂, hs₂, b₁, b₂, -⟩ := P62.exists_swap F hα h1 h3
  by_cases c1 : s₁ • ν₃ = ν₃
  swap
  · exact Or.inl ⟨s₁, hs₁, a₁, a₂, c1⟩
  by_cases c2 : s₂ • ν₂ = ν₂
  swap
  · exact Or.inr ⟨s₂, hs₂, b₁, b₂, c2⟩
  exfalso
  refine no_three_cycle F hα ((MulAction.stabilizer G α).mul_mem hs₁ hs₂) (a := ν₁) (b := ν₂)
    (c := ν₃) h1 h2 h13 h12 ?_ ?_ ?_ h3
  · rw [mul_smul, b₁, c1]
  · rw [mul_smul, b₂, a₁]
  · rw [mul_smul, c2, a₂]

theorem key_alg {N : Subgroup G} {a b c d c₁ c₂ c₃ : G} (hc₁ : c₁ ∈ N) (hc₂ : c₂ ∈ N)
    (hc₃ : c₃ ∈ N) (hc₂a : a * c₂ = c₂ * a) (hc₂d : c₂ * d = d * c₂) (hc₃d : c₃ * d = d * c₃)
    (hc₁d : c₁ * d = d * c₁) (hab : a * b = b * a * c₁) (hX : a * b * c ∈ N)
    (hY : b * c₂ * (a * c₃) * d ∈ N) : c⁻¹ * d ∈ N := by
  have e : b * c₂ * (a * c₃) * d = b * a * d * (c₂ * c₃) := by
    calc b * c₂ * (a * c₃) * d = b * (c₂ * a) * (c₃ * d) := by simp only [mul_assoc]
      _ = b * (a * c₂) * (d * c₃) := by rw [← hc₂a, hc₃d]
      _ = b * a * (c₂ * d) * c₃ := by simp only [mul_assoc]
      _ = b * a * (d * c₂) * c₃ := by rw [hc₂d]
      _ = b * a * d * (c₂ * c₃) := by simp only [mul_assoc]
  rw [e] at hY
  have h2 : b * a * d ∈ N := by
    have := N.mul_mem hY (N.inv_mem (N.mul_mem hc₂ hc₃))
    rwa [mul_inv_cancel_right] at this
  have h3 : a * b * d ∈ N := by
    have : a * b * d = b * a * d * c₁ := by
      calc a * b * d = b * a * (c₁ * d) := by rw [hab]; simp only [mul_assoc]
        _ = b * a * (d * c₁) := by rw [hc₁d]
        _ = b * a * d * c₁ := by simp only [mul_assoc]
    rw [this]
    exact N.mul_mem h2 hc₁
  have h4 := N.mul_mem (N.inv_mem hX) h3
  have : (a * b * c)⁻¹ * (a * b * d) = c⁻¹ * d := by group
  rwa [this] at h4

end P517

end CFSG.Quasithin.Fan86
