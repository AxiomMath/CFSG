module

public import CFSG.Timmesfeld.Closure.Line3
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Timmesfeld.Special.Commutator

public section

namespace CFSG.Timmesfeld.Moufang

variable {G : Type*} [Group G] {D : Set G}

theorem mul_pow_three_eq {ρ x : G} (hρ : ρ ^ 3 = 1) :
    (ρ * x) ^ 3 = (ρ * x * ρ⁻¹) * (ρ * (ρ * x * ρ⁻¹) * ρ⁻¹) * x := by
  have h : ρ⁻¹ * ρ⁻¹ = ρ := by
    rw [← mul_inv_rev, inv_eq_iff_mul_eq_one, ← pow_two, ← pow_succ, hρ]
  calc (ρ * x) ^ 3 = ρ * x * ρ * x * ρ * x := by rw [pow_three]; group
    _ = ρ * x * ρ * x * (ρ⁻¹ * ρ⁻¹) * x := by rw [h]
    _ = (ρ * x * ρ⁻¹) * (ρ * (ρ * x * ρ⁻¹) * ρ⁻¹) * x := by group

theorem mul_sq_sq_eq_of_orderOf_eq_three (hclass : ∃ d₀ : G, D = {g | IsConj d₀ g})
    (hD : IsRootInvolutionSet D) {a b c : G} (ha : a ∈ D) (hb : b ∈ D) (hc : c ∈ D)
    (hab : orderOf (a * b) = 3) (hac : Commute a c) (hacD : a * c ∈ D)
    (hcb : orderOf (c * b) = 4) : ((c * b) ^ 2 * a) ^ 2 = c := by
  have ha2 := hD.mul_self_eq_one ha
  have hb2 := hD.mul_self_eq_one hb
  have hc2 := hD.mul_self_eq_one hc
  have hainv : a⁻¹ = a := hD.inv_eq ha
  have hbinv : b⁻¹ = b := hD.inv_eq hb
  obtain ⟨hwD, hcw, -, hbcb⟩ := sq_mem_of_orderOf_eq_four hD hc hb hcb
  have hbraid : a * b * a = b * a * b := Closure.braid_of_orderOf_eq_three ha2 hb2 hab
  have hρ : (a * b) ^ 3 = 1 := by rw [← hab]; exact pow_orderOf_eq_one _
  have haca : a * c * a = c := by rw [hac.eq, mul_assoc, ha2, mul_one]
  obtain ⟨c₁, hc₁⟩ : ∃ x, x = b * c * b := ⟨_, rfl⟩
  obtain ⟨c₂, hc₂⟩ : ∃ x, x = a * c₁ * a := ⟨_, rfl⟩
  have hc1w : c₁ = c * (c * b) ^ 2 := by rw [hc₁, hbcb]
  have hc1D : c₁ ∈ D := by
    have := conj_mem_of_isClass hclass b hc
    rwa [hbinv, ← hc₁] at this
  have hc2D : c₂ ∈ D := by
    have := conj_mem_of_isClass hclass a hc1D
    rwa [hainv, ← hc₂] at this
  have hc12 := hD.mul_self_eq_one hc1D
  have hc22 := hD.mul_self_eq_one hc2D
  have hcc1 : Commute c c₁ := by rw [hc1w]; exact (Commute.refl c).mul_right hcw
  have hcc2 : Commute c c₂ := by
    have h := (Commute.conj_iff a).2 hcc1
    rwa [hainv, haca, ← hc₂] at h
  have hbc2b : b * c₂ * b = c₂ := by
    rw [hc₂, hc₁]
    calc b * (a * (b * c * b) * a) * b = (b * a * b) * c * (b * a * b) := by group
      _ = (a * b * a) * c * (a * b * a) := by rw [hbraid]
      _ = a * b * (a * c * a) * b * a := by group
      _ = a * (b * c * b) * a := by rw [haca]; group
  have hc1c2 : Commute c₁ c₂ := by
    have h := (Commute.conj_iff b).2 hcc2
    rwa [hbinv, ← hc₁, hbc2b] at h
  have e1 : a * b * c₁ * (a * b)⁻¹ = c := by
    rw [mul_inv_rev, hainv, hbinv, hc₁]
    calc a * b * (b * c * b) * (b * a) = a * (b * b) * c * (b * b) * a := by group
      _ = c := by rw [hb2, mul_one, mul_one, haca]
  have e2 : a * b * c * (a * b)⁻¹ = c₂ := by
    rw [mul_inv_rev, hainv, hbinv, hc₂, hc₁]
    group
  have hg : a * c * b = a * b * c₁ := by
    rw [hc₁]
    calc a * c * b = a * (b * b) * c * b := by rw [hb2, mul_one]
      _ = a * b * (b * c * b) := by group
  have hcube : (a * c * b) ^ 3 = c * c₂ * c₁ := by
    rw [hg, mul_pow_three_eq hρ, e1, e2]
  have hu2 : (c * c₂ * c₁) * (c * c₂ * c₁) = 1 := by
    calc (c * c₂ * c₁) * (c * c₂ * c₁) = c * c₂ * (c₁ * c) * c₂ * c₁ := by group
      _ = c * c₂ * (c * c₁) * c₂ * c₁ := by rw [hcc1.eq]
      _ = c * (c₂ * c) * c₁ * c₂ * c₁ := by group
      _ = c * (c * c₂) * c₁ * c₂ * c₁ := by rw [hcc2.eq]
      _ = (c * c) * c₂ * (c₁ * c₂) * c₁ := by group
      _ = (c * c) * c₂ * (c₂ * c₁) * c₁ := by rw [hc1c2.eq]
      _ = (c * c) * (c₂ * c₂) * (c₁ * c₁) := by group
      _ = 1 := by rw [hc2, hc22, hc12, one_mul, one_mul]
  have hu : c * c₂ * c₁ = 1 := by
    have h6 : (a * c * b) ^ 6 = 1 := by
      rw [show (6 : ℕ) = 3 * 2 by norm_num, pow_mul, hcube, pow_two, hu2]
    have hdvd : orderOf (a * c * b) ∣ 6 := orderOf_dvd_of_pow_eq_one h6
    rcases hD.orderOf_mul hacD hb with h2 | h4 | hodd
    ·
      exfalso
      have hg2 : (a * c * b) ^ 2 = 1 := by rw [← h2]; exact pow_orderOf_eq_one _
      have hgu : a * c * b = c * c₂ * c₁ := by
        rw [← hcube, pow_succ, hg2, one_mul]
      have hρu : a * b = c * c₂ := by
        calc a * b = a * b * c₁ * c₁ := by rw [mul_assoc (a * b), hc12, mul_one]
          _ = c * c₂ * c₁ * c₁ := by rw [← hg, hgu]
          _ = c * c₂ := by rw [mul_assoc (c * c₂), hc12, mul_one]
      have hρ2 : (a * b) ^ 2 = 1 := by
        rw [hρu, pow_two]
        calc c * c₂ * (c * c₂) = c * (c₂ * c) * c₂ := by group
          _ = c * (c * c₂) * c₂ := by rw [hcc2.eq]
          _ = (c * c) * (c₂ * c₂) := by group
          _ = 1 := by rw [hc2, hc22, one_mul]
      have := orderOf_dvd_of_pow_eq_one hρ2
      rw [hab] at this
      exact absurd this (by norm_num)
    · rw [h4] at hdvd
      exact absurd hdvd (by norm_num)
    · have h3 : orderOf (a * c * b) ∣ 3 := by
        have hcop : Nat.Coprime (orderOf (a * c * b)) 2 := (Nat.coprime_two_right).2 hodd
        exact hcop.dvd_of_dvd_mul_right (by rwa [show (6 : ℕ) = 3 * 2 by norm_num] at hdvd)
      rw [← hcube]
      exact orderOf_dvd_iff_pow_eq_one.1 h3
  have hc2eq : c₂ = c * c₁ := by
    calc c₂ = c * c * c₂ * c₁ * c₁ := by
          rw [hc2, one_mul, mul_assoc, hc12, mul_one]
      _ = c * (c * c₂ * c₁) * c₁ := by group
      _ = c * c₁ := by rw [hu, mul_one]
  have hw : (c * b) ^ 2 = c₂ := by
    rw [hc2eq, hc1w, ← mul_assoc, hc2, one_mul]
  have hac2a : a * c₂ * a = c₁ := by
    rw [hc₂, show a * (a * c₁ * a) * a = (a * a) * c₁ * (a * a) by group, ha2, one_mul, mul_one]
  rw [hw, pow_two]
  calc c₂ * a * (c₂ * a) = c₂ * (a * c₂ * a) := by group
    _ = c₂ * c₁ := by rw [hac2a]
    _ = c := by rw [hc2eq, mul_assoc, hc12, mul_one]

theorem mul_sq_eq_of_orderOf_eq_three (hclass : ∃ d₀ : G, D = {g | IsConj d₀ g})
    (hD : IsRootInvolutionSet D) {y x₁ x₂ c : G} (hy : y ∈ D) (hx₁ : x₁ ∈ D) (hx₂ : x₂ ∈ D)
    (hc : c ∈ D) (hx₁y : Commute x₁ y) (hx₁yD : x₁ * y ∈ D) (h4 : orderOf (x₁ * x₂) = 4)
    (h3 : orderOf (x₁ * c) = 3) (hyc : orderOf (y * c) = 4) (hw : (y * c) ^ 2 = x₂) :
    (x₁ * x₂) ^ 2 = y := by
  have key := mul_sq_sq_eq_of_orderOf_eq_three hclass hD hx₁ hc hy h3 hx₁y hx₁yD hyc
  rw [hw] at key
  rw [mul_sq_eq_mul_sq_comm (hD.mul_self_eq_one hx₁) (hD.mul_self_eq_one hx₂) h4, key]

end CFSG.Timmesfeld.Moufang
