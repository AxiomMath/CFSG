module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveL2SplitOrthA

public section

namespace CFSG.StandardType

open CFSG.LieType.RootSystem CFSG.LieType.Universal.SpecialLinear

theorem ggNEA_dot_sub_sub_eq_zero {k : ℕ} {a b p q : Fin k}
    (hap : a ≠ p) (haq : a ≠ q) (hbp : b ≠ p) (hbq : b ≠ q) :
    ggDDot (Pi.single a 1 - Pi.single b 1 : Fin k → ℤ)
      (Pi.single p 1 - Pi.single q 1) = 0 := by
  rw [sub_eq_add_neg, ← Pi.single_neg, sub_eq_add_neg, ← Pi.single_neg,
    ggDDot_single_add_single]
  simp [Pi.single_apply, hap, haq, hbp, hbq, Ne.symm hap, Ne.symm haq, Ne.symm hbp, Ne.symm hbq]

theorem ggNEA_ggDReflect_comm_of_dot {k : ℕ} {γ γ' : Fin k → ℤ}
    (hγ : ggDDot γ γ = 2) (hγ' : ggDDot γ' γ' = 2) (h : ggDDot γ γ' = 0) (u : Fin k → ℤ) :
    ggDReflect γ (ggDReflect γ' u) = ggDReflect γ' (ggDReflect γ u) := by
  have h1 : ggDDot (ggDReflect γ' u) γ = ggDDot u γ := by
    rw [ggDDot_comm (ggDReflect γ' u) γ, ggDDot_ggDReflect, h, mul_zero, sub_zero,
      ggDDot_comm γ u]
  have h2 : ggDDot (ggDReflect γ u) γ' = ggDDot u γ' := by
    rw [ggDDot_comm (ggDReflect γ u) γ', ggDDot_ggDReflect, ggDDot_comm γ' γ, h, mul_zero,
      sub_zero, ggDDot_comm γ' u]
  funext c
  simp only [ggDReflect_apply, h1, h2]
  ring

theorem ggNEA_dot_zero_of_comm {n : ℕ} {t t' : ggOrthA_WA n} {γ γ' : Fin (n + 1) → ℤ}
    (ht : ggOrthA_AReflRoot n t γ) (ht' : ggOrthA_AReflRoot n t' γ')
    (hne : t ≠ t') (hcomm : t * t' = t' * t) : ggDDot γ γ' = 0 := by
  obtain ⟨w, i, -, hw⟩ := id ht
  have key : toStd n (weylAction (isFiniteType_A n) (t * t')
        (weylAction (isFiniteType_A n) w (Pi.single i 1))) =
      toStd n (weylAction (isFiniteType_A n) (t' * t)
        (weylAction (isFiniteType_A n) w (Pi.single i 1))) := by
    rw [hcomm]
  rw [weylAction_mul_apply, weylAction_mul_apply, ggOrthA_refl_action ht, ggOrthA_refl_action ht',
    ggOrthA_refl_action ht', ggOrthA_refl_action ht, hw] at key
  have h2 : ggDDot γ γ = 2 := by
    obtain ⟨p, q, hpq, hγ⟩ := ggOrthA_refl_mem ht
    rw [hγ]
    exact ggOrthA_dot_self hpq
  have h2' : ggDDot γ' γ' = 2 := by
    obtain ⟨p, q, hpq, hγ⟩ := ggOrthA_refl_mem ht'
    rw [hγ]
    exact ggOrthA_dot_self hpq
  rcases ggDReflect_comm_dot h2 h2' key with h0 | h0 | h0
  · exact h0
  · exact absurd (ggOrthA_refl_unique ht ht' (Or.inl h0)) hne
  · exact absurd (ggOrthA_refl_unique ht ht' (Or.inr h0)) hne

theorem ggNEA_comm_of_disj_supp {n : ℕ} {t t' : ggOrthA_WA n} {a b p q : Fin (n + 1)}
    (ht : ggOrthA_AReflRoot n t (Pi.single a 1 - Pi.single b 1))
    (ht' : ggOrthA_AReflRoot n t' (Pi.single p 1 - Pi.single q 1))
    (hab : a ≠ b) (hpq : p ≠ q)
    (hap : a ≠ p) (haq : a ≠ q) (hbp : b ≠ p) (hbq : b ≠ q) :
    t * t' = t' * t := by
  apply weylAction_injective (isFiniteType_A n)
  apply LinearMap.ext
  intro v
  apply toStd_injective n
  rw [map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, ggOrthA_refl_action ht,
    ggOrthA_refl_action ht', ggOrthA_refl_action ht', ggOrthA_refl_action ht]
  exact ggNEA_ggDReflect_comm_of_dot (ggOrthA_dot_self hab) (ggOrthA_dot_self hpq)
    (ggNEA_dot_sub_sub_eq_zero hap haq hbp hbq) (toStd n v)

theorem ggNEA_meet_three_disjoint_pairs {k : ℕ} {a b p₁ q₁ p₂ q₂ p₃ q₃ : Fin k}
    (h12 : p₁ ≠ p₂) (h12' : p₁ ≠ q₂) (h12'' : q₁ ≠ p₂) (h12''' : q₁ ≠ q₂)
    (h13 : p₁ ≠ p₃) (h13' : p₁ ≠ q₃) (h13'' : q₁ ≠ p₃) (h13''' : q₁ ≠ q₃)
    (h23 : p₂ ≠ p₃) (h23' : p₂ ≠ q₃) (h23'' : q₂ ≠ p₃) (h23''' : q₂ ≠ q₃)
    (m1 : a = p₁ ∨ a = q₁ ∨ b = p₁ ∨ b = q₁)
    (m2 : a = p₂ ∨ a = q₂ ∨ b = p₂ ∨ b = q₂)
    (m3 : a = p₃ ∨ a = q₃ ∨ b = p₃ ∨ b = q₃) : False := by
  omega

theorem ggNEA_fork_absurd_WA {n : ℕ} {t₀ t₁ t₂ t₃ : ggOrthA_WA n}
    {γ₀ γ₁ γ₂ γ₃ : Fin (n + 1) → ℤ}
    (hγ₀ : ggOrthA_AReflRoot n t₀ γ₀) (hγ₁ : ggOrthA_AReflRoot n t₁ γ₁)
    (hγ₂ : ggOrthA_AReflRoot n t₂ γ₂) (hγ₃ : ggOrthA_AReflRoot n t₃ γ₃)
    (h12 : t₁ * t₂ = t₂ * t₁) (h13 : t₁ * t₃ = t₃ * t₁) (h23 : t₂ * t₃ = t₃ * t₂)
    (hn12 : t₁ ≠ t₂) (hn13 : t₁ ≠ t₃) (hn23 : t₂ ≠ t₃)
    (hn01 : t₀ * t₁ ≠ t₁ * t₀) (hn02 : t₀ * t₂ ≠ t₂ * t₀) (hn03 : t₀ * t₃ ≠ t₃ * t₀) :
    False := by
  obtain ⟨a, b, hab, hγ₀'⟩ := ggOrthA_refl_mem hγ₀
  obtain ⟨p₁, q₁, hp₁q₁, hγ₁'⟩ := ggOrthA_refl_mem hγ₁
  obtain ⟨p₂, q₂, hp₂q₂, hγ₂'⟩ := ggOrthA_refl_mem hγ₂
  obtain ⟨p₃, q₃, hp₃q₃, hγ₃'⟩ := ggOrthA_refl_mem hγ₃
  rw [hγ₀'] at hγ₀
  rw [hγ₁'] at hγ₁
  rw [hγ₂'] at hγ₂
  rw [hγ₃'] at hγ₃
  have d12 := ggOrthA_disj_of_dot hp₁q₁ hp₂q₂ (ggNEA_dot_zero_of_comm hγ₁ hγ₂ hn12 h12)
  have d13 := ggOrthA_disj_of_dot hp₁q₁ hp₃q₃ (ggNEA_dot_zero_of_comm hγ₁ hγ₃ hn13 h13)
  have d23 := ggOrthA_disj_of_dot hp₂q₂ hp₃q₃ (ggNEA_dot_zero_of_comm hγ₂ hγ₃ hn23 h23)
  have m1 : a = p₁ ∨ a = q₁ ∨ b = p₁ ∨ b = q₁ := by
    by_contra h
    simp only [not_or] at h
    exact hn01 (ggNEA_comm_of_disj_supp hγ₀ hγ₁ hab hp₁q₁ h.1 h.2.1 h.2.2.1 h.2.2.2)
  have m2 : a = p₂ ∨ a = q₂ ∨ b = p₂ ∨ b = q₂ := by
    by_contra h
    simp only [not_or] at h
    exact hn02 (ggNEA_comm_of_disj_supp hγ₀ hγ₂ hab hp₂q₂ h.1 h.2.1 h.2.2.1 h.2.2.2)
  have m3 : a = p₃ ∨ a = q₃ ∨ b = p₃ ∨ b = q₃ := by
    by_contra h
    simp only [not_or] at h
    exact hn03 (ggNEA_comm_of_disj_supp hγ₀ hγ₃ hab hp₃q₃ h.1 h.2.1 h.2.2.1 h.2.2.2)
  obtain ⟨d12a, d12b, d12c, d12d⟩ := d12
  obtain ⟨d13a, d13b, d13c, d13d⟩ := d13
  obtain ⟨d23a, d23b, d23c, d23d⟩ := d23
  exact ggNEA_meet_three_disjoint_pairs d12a d12b d12c d12d d13a d13b d13c d13d
    d23a d23b d23c d23d m1 m2 m3

end CFSG.StandardType

end
