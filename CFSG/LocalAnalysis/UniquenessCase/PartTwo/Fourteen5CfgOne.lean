module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.K330Cfg.ExclAll

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Open Subgroup
open CFSG.ComponentClassification (Layer.subgroup)

namespace Cfg145

variable {K : Type} [Group K] [Finite K] {M X₁ X₂ P : Subgroup K}

theorem false_of_le_component (c : Cfg145 M X₁ X₂ P) (hE : K330Cfg.ExclAll) {J : Subgroup K}
    (hJ : IsComponentOf J ⊤) (hJu : ∀ J' : Subgroup K, IsComponentOf J' ⊤ → J' = J)
    (hXJ : X₁ ⊔ X₂ ≤ J) : False :=
  c.false_of_exclAll hE hJ hJu hXJ

private theorem false_of_inf_eq_bot_of_le (c : Cfg145 M X₁ X₂ P) (hKB : KThreeInner)
    {J : Subgroup K} (hJ : IsComponentOf J ⊤)
    (hJu : ∀ J' : Subgroup K, IsComponentOf J' ⊤ → J' = J)
    (hJnorm : normalizer (J : Set K) = ⊤) (hnot9 : ¬ 9 ∣ Nat.card J) {Y : Subgroup K}
    (hYX : Y ≤ X₁ ⊔ X₂) (hY : Nat.card Y = 3) (hYJ : Y ⊓ J = ⊥) : False := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hYne : Y ≠ ⊥ := by
    intro hbot
    rw [hbot, Subgroup.card_bot] at hY
    norm_num at hY
  obtain ⟨x, hx1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hYne
  have hxY : (x : K) ∈ Y := x.2
  have hx_ne : (x : K) ≠ 1 := fun h => hx1 (Subtype.ext h)
  have hxN : (x : K) ∈ normalizer (J : Set K) := by
    rw [hJnorm]
    exact Subgroup.mem_top (x : K)
  have hx3 : (x : K) ^ 3 = 1 := by
    have hdvd : orderOf (x : K) ∣ 3 := by
      have h := Subgroup.orderOf_dvd_natCard Y hxY
      rwa [hY] at h
    exact orderOf_dvd_iff_pow_eq_one.mp hdvd
  obtain ⟨j, hjJ, hj⟩ := hKB K c.isKGroup J (c.isSimpleGroup_of_isComponentOf hJ)
    (c.three_dvd_card_of_isComponentOf hJ) hnot9 (x : K) hxN hx3
  have hcent : centralizer (J : Set K) = ⊥ := by
    rw [← layer_eq_of_forall hJ hJu]
    exact c.centralizer_layer_eq_bot
  have hg : (j : K)⁻¹ * (x : K) ∈ centralizer (J : Set K) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have h2 : ((j : K)⁻¹ * (x : K)) * y * ((j : K)⁻¹ * (x : K))⁻¹ = y := by
      have h3 : (j : K)⁻¹ * ((x : K) * y * (x : K)⁻¹) * (j : K) = y := by
        rw [hj y hy]
        group
      calc ((j : K)⁻¹ * (x : K)) * y * ((j : K)⁻¹ * (x : K))⁻¹
          = (j : K)⁻¹ * ((x : K) * y * (x : K)⁻¹) * (j : K) := by group
        _ = y := h3
    have h4 : ((j : K)⁻¹ * (x : K)) * y = y * ((j : K)⁻¹ * (x : K)) := by
      have h5 := congrArg (· * ((j : K)⁻¹ * (x : K))) h2
      simpa [mul_assoc] using h5
    exact h4.symm
  have hx_eq : (x : K) = (j : K) := by
    have h := Subgroup.mem_bot.mp (hcent ▸ hg)
    rw [inv_mul_eq_one] at h
    exact h.symm
  have hxJ : (x : K) ∈ J := by rw [hx_eq]; exact hjJ
  have hxbot : (x : K) ∈ (⊥ : Subgroup K) := by
    rw [← hYJ]
    exact ⟨hxY, hxJ⟩
  exact hx_ne (Subgroup.mem_bot.mp hxbot)

theorem false_of_card_inf_eq_three (c : Cfg145 M X₁ X₂ P) (hKB : KThreeInner) {J : Subgroup K}
    (hJ : IsComponentOf J ⊤) (hJu : ∀ J' : Subgroup K, IsComponentOf J' ⊤ → J' = J)
    (hXJ : Nat.card ↥((X₁ ⊔ X₂) ⊓ J) = 3) : False := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hJnorm : normalizer (J : Set K) = ⊤ := by
    rw [Subgroup.normalizer_eq_top_iff, Subgroup.normal_iff_map_conj_eq]
    intro k
    exact hJu _ (isComponentOf_map_conj hJ k)
  have hisSylow : CFSG.ABGLocalTools.IsSylowOf 3 ((X₁ ⊔ X₂) ⊓ J) J :=
    c.isSylowOf_inf_of_isComponentOf hJ
  have hfac : (Nat.card J).factorization 3 = 1 := by
    have h : 3 ^ (Nat.card J).factorization 3 = 3 ^ 1 := by
      rw [← hisSylow.card_eq, hXJ]
      norm_num
    exact Nat.pow_right_injective (by norm_num : 2 ≤ 3) h
  have hnot9 : ¬ 9 ∣ Nat.card J := by
    intro h9
    have h2 : 2 ≤ (Nat.card J).factorization 3 := by
      refine (Nat.prime_three.pow_dvd_iff_le_factorization (n := Nat.card J) (k := 2)
        (Nat.card_ne_zero.mpr ⟨⟨1⟩, inferInstance⟩)).mp ?_
      simpa using h9
    rw [hfac] at h2
    norm_num at h2
  obtain ⟨d, hdX, hd₁, hd₂⟩ := c.inversion true false
  have hd₁' : ∀ x ∈ X₁, d * x * d⁻¹ = x⁻¹ := by
    intro x hx
    simpa using hd₁ x hx
  have hd₂' : ∀ x ∈ X₂, d * x * d⁻¹ = x := by
    intro x hx
    simpa using hd₂ x hx
  have hdZ : d ∈ normalizer (((X₁ ⊔ X₂) ⊓ J : Subgroup K) : Set K) :=
    Subgroup.inf_normalizer_le_normalizer_inf (H := X₁ ⊔ X₂) (K := J)
      ⟨hdX, by rw [hJnorm]; exact Subgroup.mem_top d⟩
  have hZ := c.eq_left_or_eq_right inf_le_left hXJ hdZ hd₁' hd₂'
  rcases hZ with hZ | hZ
  · refine false_of_inf_eq_bot_of_le c hKB hJ hJu hJnorm hnot9 le_sup_right c.card_right ?_
    have hle : X₂ ⊓ J ≤ X₁ := by
      calc X₂ ⊓ J ≤ (X₁ ⊔ X₂) ⊓ J := inf_le_inf le_sup_right le_rfl
        _ = X₁ := hZ
    exact bot_unique ((le_inf hle inf_le_left).trans (le_of_eq c.inf_eq_bot))
  · refine false_of_inf_eq_bot_of_le c hKB hJ hJu hJnorm hnot9 le_sup_left c.card_left ?_
    have hle : X₁ ⊓ J ≤ X₂ := by
      calc X₁ ⊓ J ≤ (X₁ ⊔ X₂) ⊓ J := inf_le_inf le_sup_left le_rfl
        _ = X₂ := hZ
    exact bot_unique ((le_inf inf_le_left hle).trans (le_of_eq c.inf_eq_bot))

theorem false_of_one_component (c : Cfg145 M X₁ X₂ P) (hE : K330Cfg.ExclAll) (hKB : KThreeInner)
    {J : Subgroup K} (hJ : IsComponentOf J ⊤)
    (hJu : ∀ J' : Subgroup K, IsComponentOf J' ⊤ → J' = J) : False := by
  have hdvd : Nat.card ↥((X₁ ⊔ X₂) ⊓ J) ∣ 9 := by
    rw [← c.card_sup]
    exact Subgroup.card_dvd_of_le inf_le_left
  have hne1 : Nat.card ↥((X₁ ⊔ X₂) ⊓ J) ≠ 1 := by
    intro h
    exact c.inf_ne_bot_of_isComponentOf hJ (Subgroup.card_eq_one.mp h)
  have hdvd' : Nat.card ↥((X₁ ⊔ X₂) ⊓ J) ∣ 3 ^ 2 := by
    rw [show (9 : ℕ) = 3 ^ 2 by norm_num] at hdvd
    exact hdvd
  obtain ⟨k, hk, hk_eq⟩ := (Nat.dvd_prime_pow (p := 3) (m := 2) Nat.prime_three).1 hdvd'
  interval_cases k
  · simp only [pow_zero] at hk_eq
    exact hne1 hk_eq
  · exact false_of_card_inf_eq_three c hKB hJ hJu (by simpa using hk_eq)
  · have hEq : (X₁ ⊔ X₂) ⊓ J = X₁ ⊔ X₂ :=
      Subgroup.eq_of_le_of_card_ge inf_le_left (by
        rw [c.card_sup]
        simpa using hk_eq.symm.le)
    exact false_of_le_component c hE hJ hJu (inf_eq_left.mp hEq)

end Cfg145

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
