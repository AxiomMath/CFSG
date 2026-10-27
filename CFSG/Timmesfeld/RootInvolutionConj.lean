module

public import CFSG.Timmesfeld.Bridge.RootStructQD
public import CFSG.Open.LocalVocabulary

public section

namespace CFSG.Timmesfeld

variable {Γ : Type*} [Group Γ]

theorem orderOf_mul_comm_aux (x y : Γ) : orderOf (y * x) = orderOf (x * y) := by
  have e : y * x = x⁻¹ * (x * y) * x⁻¹⁻¹ := by group
  rw [e]
  exact (SemiconjBy.orderOf_eq x⁻¹ (show x⁻¹ * (x * y) = x⁻¹ * (x * y) * x⁻¹⁻¹ * x⁻¹ by group)).symm

theorem exists_conj_or_conj_mul_of_odd_partner [Finite Γ] {D : Set Γ}
    (hD : IsRootInvolutionSet D) (hN : ∀ g x : Γ, x ∈ D → g * x * g⁻¹ ∈ D)
    {a b : Γ} (ha : a ∈ D) (hb : b ∈ D) (hab : a ≠ b) (hc : a * b = b * a) (habD : a * b ∈ D)
    (hodd : ∃ c ∈ D, Odd (orderOf (a * c)) ∧ a * c ≠ 1) :
    (∃ g : Γ, g * a * g⁻¹ = b) ∨ ∃ g : Γ, g * a * g⁻¹ = a * b := by
  obtain ⟨c, hcD, hoddc, hac1⟩ := hodd
  have ha2 := hD.mul_self_eq_one ha
  have hb2 := hD.mul_self_eq_one hb
  have hc2 := hD.mul_self_eq_one hcD
  have hn1 : orderOf (a * c) ≠ 1 := fun h => hac1 (orderOf_eq_one_iff.mp h)
  have hnc : ¬ Commute a c := by
    intro hcm
    have hsq : (a * c) ^ 2 = 1 := (commute_iff_mul_sq_eq_one ha2 hc2).1 hcm
    have h2 : orderOf (a * c) ∣ 2 := orderOf_dvd_of_pow_eq_one hsq
    rcases (Nat.dvd_prime Nat.prime_two).1 h2 with h | h
    · exact hn1 h
    · rw [h] at hoddc
      exact absurd hoddc (by decide)
  rcases hD.orderOf_mul hb hcD with hm | hm | hm
  ·
    exfalso
    have hbc : b * c = c * b :=
      ((commute_iff_mul_sq_eq_one hb2 hc2).2 (by rw [← hm]; exact pow_orderOf_eq_one _)).eq
    have hbt : Commute b (a * c) := by
      show b * (a * c) = (a * c) * b
      calc b * (a * c) = (b * a) * c := by rw [mul_assoc]
        _ = (a * b) * c := by rw [hc]
        _ = a * (b * c) := by rw [mul_assoc]
        _ = a * (c * b) := by rw [hbc]
        _ = (a * c) * b := by rw [mul_assoc]
    have hu : (a * b) * c = (a * c) * b := by
      calc (a * b) * c = a * (b * c) := by rw [mul_assoc]
        _ = a * (c * b) := by rw [hbc]
        _ = (a * c) * b := by rw [mul_assoc]
    have hpow : ∀ k : ℕ, ((a * b) * c) ^ k = (a * c) ^ k * b ^ k := fun k => by
      rw [hu]; exact hbt.symm.mul_pow k
    rcases hD.orderOf_mul habD hcD with h | h | h
    · have h1 : ((a * b) * c) ^ 2 = 1 := by rw [← h]; exact pow_orderOf_eq_one _
      rw [hpow, pow_two b, hb2, mul_one] at h1
      have h2 : orderOf (a * c) ∣ 2 := orderOf_dvd_of_pow_eq_one h1
      rcases (Nat.dvd_prime Nat.prime_two).1 h2 with h' | h'
      · exact hn1 h'
      · rw [h'] at hoddc
        exact absurd hoddc (by decide)
    · have h1 : ((a * b) * c) ^ 4 = 1 := by rw [← h]; exact pow_orderOf_eq_one _
      have hb4 : b ^ 4 = 1 := by
        rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, pow_two b, hb2, one_pow]
      rw [hpow, hb4, mul_one] at h1
      have h2 : orderOf (a * c) ∣ 4 := orderOf_dvd_of_pow_eq_one h1
      have h3 : orderOf (a * c) ∣ 2 ^ 2 := by simpa using h2
      obtain ⟨i, hi, hi'⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 h3
      interval_cases i
      · exact hn1 (by simpa using hi')
      · rw [hi'] at hoddc
        exact absurd hoddc (by decide)
      · rw [hi'] at hoddc
        exact absurd hoddc (by decide)
    · obtain ⟨k, hk⟩ := h
      have h1 : ((a * b) * c) ^ (2 * k + 1) = 1 := by rw [← hk]; exact pow_orderOf_eq_one _
      have hbk : b ^ (2 * k + 1) = b := by
        rw [pow_succ, pow_mul, pow_two b, hb2, one_pow, one_mul]
      rw [hpow, hbk] at h1
      have hbinv : (a * c) ^ (2 * k + 1) = b⁻¹ := mul_eq_one_iff_eq_inv.1 h1
      rw [hD.inv_eq hb] at hbinv
      have hmem : b ∈ Subgroup.zpowers (a * c) := by
        rw [← hbinv]
        exact Subgroup.pow_mem _ (Subgroup.mem_zpowers _) _
      have hdvd : orderOf b ∣ orderOf (a * c) := orderOf_dvd_of_mem_zpowers hmem
      rw [hD.orderOf_eq_two hb] at hdvd
      obtain ⟨l, hl⟩ := hoddc
      omega
  ·
    right
    have h4 : orderOf (c * b) = 4 := by rw [orderOf_mul_comm_aux]; exact hm
    obtain ⟨x, hxD, -, -, -, hx⟩ :=
      Bridge.exists_conj_eq_mul_of_odd_special hD hN ha hcD hb hnc hoddc h4
        (show Commute a b from hc) habD
    exact ⟨x, by rw [hD.inv_eq hxD]; exact hx⟩
  ·
    left
    obtain ⟨g₁, -, hg₁⟩ := exists_conj_of_odd_orderOf_mul ha2 hc2 hoddc
    obtain ⟨g₂, -, hg₂⟩ := exists_conj_of_odd_orderOf_mul hb2 hc2 hm
    refine ⟨g₂⁻¹ * g₁, ?_⟩
    calc g₂⁻¹ * g₁ * a * (g₂⁻¹ * g₁)⁻¹ = g₂⁻¹ * (g₁ * a * g₁⁻¹) * g₂ := by group
      _ = g₂⁻¹ * c * g₂ := by rw [hg₁]
      _ = g₂⁻¹ * (g₂ * b * g₂⁻¹) * g₂ := by rw [hg₂]
      _ = b := by group

theorem exists_conj_of_commuting_pair [Finite Γ] {D : Set Γ}
    (hD : IsRootInvolutionSet D) (hN : ∀ g x : Γ, x ∈ D → g * x * g⁻¹ ∈ D)
    (hodd : ∀ a ∈ D, ∃ c ∈ D, Odd (orderOf (a * c)) ∧ a * c ≠ 1)
    {a b : Γ} (ha : a ∈ D) (hb : b ∈ D) (hab : a ≠ b) (hc : a * b = b * a)
    (habD : a * b ∈ D) : ∃ g : Γ, g * a * g⁻¹ = b := by
  have hbaD : b * a ∈ D := by rw [← hc]; exact habD
  rcases exists_conj_or_conj_mul_of_odd_partner hD hN ha hb hab hc habD (hodd a ha)
    with h | ⟨g₁, hg₁⟩
  · exact h
  rcases exists_conj_or_conj_mul_of_odd_partner hD hN hb ha hab.symm hc.symm hbaD (hodd b hb)
    with ⟨g₂, hg₂⟩ | ⟨g₂, hg₂⟩
  · refine ⟨g₂⁻¹, ?_⟩
    calc g₂⁻¹ * a * g₂⁻¹⁻¹ = g₂⁻¹ * (g₂ * b * g₂⁻¹) * g₂ := by rw [hg₂]; group
      _ = b := by group
  · refine ⟨g₂⁻¹ * g₁, ?_⟩
    calc g₂⁻¹ * g₁ * a * (g₂⁻¹ * g₁)⁻¹ = g₂⁻¹ * (g₁ * a * g₁⁻¹) * g₂ := by group
      _ = g₂⁻¹ * (a * b) * g₂ := by rw [hg₁]
      _ = g₂⁻¹ * (b * a) * g₂ := by rw [hc]
      _ = g₂⁻¹ * (g₂ * b * g₂⁻¹) * g₂ := by rw [hg₂]
      _ = b := by group

theorem isRootInvolutionSet_image_ne_one {R K : Type*} [Group R] [Group K] (π : R →* K)
    {D : Set R} (hD : IsRootInvolutionSet D) :
    IsRootInvolutionSet (π '' {x | x ∈ D ∧ π x ≠ 1}) := by
  obtain ⟨h1, h2, h3⟩ := hD
  refine ⟨?_, ?_, ?_⟩
  · rintro _ ⟨x, ⟨hx, hx1⟩, rfl⟩
    refine orderOf_eq_prime ?_ hx1
    have hx2 : x ^ 2 = 1 := by rw [← h1 x hx]; exact pow_orderOf_eq_one x
    rw [← map_pow, hx2, map_one]
  · rintro _ ⟨x, ⟨hx, hx1⟩, rfl⟩ _ ⟨w, ⟨hw, hw1⟩, rfl⟩
    have hdvd : orderOf (π x * π w) ∣ orderOf (x * w) := by
      rw [← map_mul]
      exact orderOf_map_dvd π _
    rcases h2 x hx w hw with h | h | h
    · rw [h] at hdvd
      rcases (Nat.dvd_prime Nat.prime_two).1 hdvd with h' | h'
      · exact Or.inr (Or.inr (by rw [h']; exact odd_one))
      · exact Or.inl h'
    · rw [h] at hdvd
      have h22 : orderOf (π x * π w) ∣ 2 ^ 2 := by simpa using hdvd
      rcases (Nat.dvd_prime_pow Nat.prime_two).1 h22 with ⟨i, hi, hi'⟩
      interval_cases i
      · exact Or.inr (Or.inr (by rw [hi']; exact odd_one))
      · exact Or.inl (by simpa using hi')
      · exact Or.inr (Or.inl (by simpa using hi'))
    · exact Or.inr (Or.inr (Odd.of_dvd_nat h hdvd))
  · rintro _ ⟨x, ⟨hx, hx1⟩, rfl⟩ _ ⟨w, ⟨hw, hw1⟩, rfl⟩ h4
    have hdvd : orderOf (π x * π w) ∣ orderOf (x * w) := by
      rw [← map_mul]
      exact orderOf_map_dvd π _
    have h4' : orderOf (x * w) = 4 := by
      rw [h4] at hdvd
      rcases h2 x hx w hw with h | h | h
      · rw [h] at hdvd
        exact absurd (Nat.le_of_dvd (by norm_num) hdvd) (by norm_num)
      · exact h
      · exact absurd (Odd.of_dvd_nat h hdvd) (by decide)
    have hsq : π ((x * w) ^ 2) = (π x * π w) ^ 2 := by simp [map_pow, map_mul]
    refine ⟨(x * w) ^ 2, ⟨h3 x hx w hw h4', ?_⟩, hsq⟩
    rw [hsq]
    exact pow_ne_one_of_lt_orderOf (by norm_num) (by omega)

theorem isRootInvolutionSet_subtype {G : Type*} [Group G] {S : Subgroup G} {D : Set G}
    (hD : IsRootInvolutionSet D) : IsRootInvolutionSet {x : ↥S | (x : G) ∈ D} := by
  obtain ⟨h1, h2, h3⟩ := hD
  refine ⟨fun x hx => ?_, fun x hx y hy => ?_, fun x hx y hy h4 => ?_⟩
  · rw [← Subgroup.orderOf_coe]; exact h1 _ hx
  · rw [← Subgroup.orderOf_coe, Subgroup.coe_mul]; exact h2 _ hx _ hy
  · rw [← Subgroup.orderOf_coe, Subgroup.coe_mul] at h4
    have := h3 _ hx _ hy h4
    simpa using this

theorem exists_odd_partner_of_not_mem_pCoreOf [Finite Γ] {Y : Subgroup Γ} {D : Set Γ}
    (hD : IsRootInvolutionSet D) (hDY : D ⊆ Y) (hN : ∀ y ∈ Y, ∀ x ∈ D, y * x * y⁻¹ ∈ D)
    {a : Γ} (ha : a ∈ D) (hO : a ∉ CFSG.Open.pCoreOf 2 Y) :
    ∃ y ∈ Y, Odd (orderOf (a * (y * a * y⁻¹))) ∧ a * (y * a * y⁻¹) ≠ 1 := by
  by_contra hne
  push Not at hne
  apply hO
  have hD' := isRootInvolutionSet_subtype (S := Y) hD
  have ha' : (⟨a, hDY ha⟩ : ↥Y) ∈ {x : ↥Y | (x : Γ) ∈ D} := ha
  have hmem : (⟨a, hDY ha⟩ : ↥Y) ∈ CFSG.pCore 2 ↥Y := by
    rw [CFSG.BaerSuzuki.baer_suzuki_iff]
    intro g
    have hg : g * ⟨a, hDY ha⟩ * g⁻¹ ∈ {x : ↥Y | (x : Γ) ∈ D} := by
      show ((g * ⟨a, hDY ha⟩ * g⁻¹ : ↥Y) : Γ) ∈ D
      simpa using hN g g.2 a ha
    apply isPGroup_two_closure_pair (hD'.mul_self_eq_one ha') (hD'.mul_self_eq_one hg)
    rcases hD'.orderOf_mul ha' hg with h | h | h
    · rw [show 2 ^ 2 = 2 * 2 by norm_num, pow_mul, ← h, pow_orderOf_eq_one, one_pow]
    · rw [show 2 ^ 2 = 4 by norm_num, ← h, pow_orderOf_eq_one]
    · have h1 : (⟨a, hDY ha⟩ : ↥Y) * (g * ⟨a, hDY ha⟩ * g⁻¹) = 1 := by
        apply Subtype.ext
        have := hne g g.2 (by
          have h' : Odd (orderOf (((⟨a, hDY ha⟩ : ↥Y) * (g * ⟨a, hDY ha⟩ * g⁻¹) : ↥Y) : Γ)) := by
            rwa [← Subgroup.orderOf_coe] at h
          simpa using h')
        simpa using this
      rw [h1, one_pow]
  exact ⟨⟨a, hDY ha⟩, hmem, rfl⟩

theorem exists_conj_of_commuting_pair_sub [Finite Γ] {Y : Subgroup Γ} {D : Set Γ}
    (hD : IsRootInvolutionSet D) (hDY : D ⊆ Y) (hN : ∀ y ∈ Y, ∀ x ∈ D, y * x * y⁻¹ ∈ D)
    (hodd : ∀ a ∈ D, ∃ c ∈ D, Odd (orderOf (a * c)) ∧ a * c ≠ 1)
    {a b : Γ} (ha : a ∈ D) (hb : b ∈ D) (hab : a ≠ b) (hc : a * b = b * a)
    (habD : a * b ∈ D) : ∃ y ∈ Y, y * a * y⁻¹ = b := by
  have hD' := isRootInvolutionSet_subtype (S := Y) hD
  have hN' : ∀ g x : ↥Y, x ∈ {x : ↥Y | (x : Γ) ∈ D} → g * x * g⁻¹ ∈ {x : ↥Y | (x : Γ) ∈ D} := by
    intro g x hx
    show ((g * x * g⁻¹ : ↥Y) : Γ) ∈ D
    simpa using hN g g.2 x hx
  have hodd' : ∀ a' ∈ {x : ↥Y | (x : Γ) ∈ D}, ∃ c ∈ {x : ↥Y | (x : Γ) ∈ D},
      Odd (orderOf (a' * c)) ∧ a' * c ≠ 1 := by
    intro a' ha'
    obtain ⟨c, hcD, hoc, hc1⟩ := hodd a' ha'
    refine ⟨⟨c, hDY hcD⟩, hcD, ?_, ?_⟩
    · rw [← Subgroup.orderOf_coe]; simpa using hoc
    · intro h
      apply hc1
      simpa using congrArg Subtype.val h
  obtain ⟨g, hg⟩ := exists_conj_of_commuting_pair hD' hN' hodd'
    (a := ⟨a, hDY ha⟩) (b := ⟨b, hDY hb⟩) ha hb
    (fun h => hab (congrArg Subtype.val h)) (Subtype.ext hc) (by
      show ((⟨a, hDY ha⟩ * ⟨b, hDY hb⟩ : ↥Y) : Γ) ∈ D
      simpa using habD)
  exact ⟨g, g.2, by simpa using congrArg Subtype.val hg⟩

end CFSG.Timmesfeld
