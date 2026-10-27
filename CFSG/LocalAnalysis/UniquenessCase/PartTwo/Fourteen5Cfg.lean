module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Fourteen5Inputs
public import CFSG.GroupTheory.QuasisimpleCommutingProductBound

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Open Subgroup
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)

namespace Cfg145

variable {K : Type} [Group K] [Finite K] {M X₁ X₂ P : Subgroup K}

theorem symm (c : Cfg145 M X₁ X₂ P) : Cfg145 M X₂ X₁ P := by
  refine
    { isKGroup := c.isKGroup
      strong := c.strong
      card_left := c.card_right
      card_right := c.card_left
      card_sup := ?_
      isSylowOf_three := ?_
      normal_eq_bot := c.normal_eq_bot
      normalizer_le := ?_
      normalizer_left_le := c.normalizer_right_le
      normalizer_right_le := c.normalizer_left_le
      inversion := ?_
      permutes := ?_
      isSylowOf_seven := c.isSylowOf_seven
      le_centralizer := ?_
      isCyclic := c.isCyclic
      exists_isSylowOf_two := c.exists_isSylowOf_two }
  · simpa [sup_comm] using c.card_sup
  · simpa [sup_comm] using c.isSylowOf_three
  · simpa [sup_comm] using c.normalizer_le
  · intro s₁ s₂
    obtain ⟨n, hn, h₁, h₂⟩ := c.inversion s₂ s₁
    exact ⟨n, by simpa [sup_comm] using hn, h₂, h₁⟩
  · intro n hn
    have hn' : n ∈ normalizer ((X₁ ⊔ X₂ : Subgroup K) : Set K) := by
      simpa [sup_comm] using hn
    rcases c.permutes n hn' with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
    · exact Or.inl ⟨h₂, h₁⟩
    · exact Or.inr ⟨h₂, h₁⟩
  · simpa [sup_comm] using c.le_centralizer

theorem inf_eq_bot (c : Cfg145 M X₁ X₂ P) : X₁ ⊓ X₂ = ⊥ := by
  by_contra hne
  have hcard_ne_one : Nat.card (X₁ ⊓ X₂ : Subgroup K) ≠ 1 := fun h =>
    hne (Subgroup.card_eq_one.mp h)
  have hdvd : Nat.card (X₁ ⊓ X₂ : Subgroup K) ∣ 3 := by
    have h := Subgroup.card_dvd_of_le (inf_le_left : X₁ ⊓ X₂ ≤ X₁)
    rwa [c.card_left] at h
  have hcard_inf : Nat.card (X₁ ⊓ X₂ : Subgroup K) = 3 := by
    rcases (Nat.dvd_prime Nat.prime_three).1 hdvd with h | h
    · exact absurd h hcard_ne_one
    · exact h
  have hX₁ : (X₁ ⊓ X₂ : Subgroup K) = X₁ :=
    Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [hcard_inf, c.card_left])
  have hX₂ : (X₁ ⊓ X₂ : Subgroup K) = X₂ :=
    Subgroup.eq_of_le_of_card_ge inf_le_right (by rw [hcard_inf, c.card_right])
  have hEq : X₁ = X₂ := hX₁.symm.trans hX₂
  have hsup : X₁ ⊔ X₂ = X₁ := by rw [hEq, sup_idem]
  have h9 : Nat.card X₁ = 9 := by
    rw [← hsup]
    exact c.card_sup
  rw [c.card_left] at h9
  exact absurd h9 (by norm_num)

theorem isElemAbelian (c : Cfg145 M X₁ X₂ P) : IsElemAbelian 3 (X₁ ⊔ X₂) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hcomm : IsMulCommutative ↥(X₁ ⊔ X₂) :=
    IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := 3) (by rw [c.card_sup]; norm_num)
  refine ⟨hcomm, ?_⟩
  have hcomm' : ∀ x ∈ X₁, ∀ y ∈ X₂, x * y = y * x := by
    intro x hx y hy
    exact congrArg Subtype.val (hcomm.is_comm.comm
      (⟨x, Subgroup.mem_sup_left hx⟩ : ↥(X₁ ⊔ X₂)) ⟨y, Subgroup.mem_sup_right hy⟩)
  have hset := (CFSG.GroupTheory.card_sup_mul_card_inf_of_commute X₁ X₂ hcomm').2
  intro x hx
  obtain ⟨x₁, hx₁, x₂, hx₂, hx_eq⟩ := Set.mem_mul.mp (by rw [← hset]; exact hx)
  have hcx : Commute x₁ x₂ := hcomm' x₁ hx₁ x₂ hx₂
  have hx₁3 : x₁ ^ 3 = 1 := by
    have hdvd : orderOf x₁ ∣ 3 := by
      have h := Subgroup.orderOf_dvd_natCard X₁ hx₁
      rwa [c.card_left] at h
    exact orderOf_dvd_iff_pow_eq_one.mp hdvd
  have hx₂3 : x₂ ^ 3 = 1 := by
    have hdvd : orderOf x₂ ∣ 3 := by
      have h := Subgroup.orderOf_dvd_natCard X₂ hx₂
      rwa [c.card_right] at h
    exact orderOf_dvd_iff_pow_eq_one.mp hdvd
  rw [← hx_eq, hcx.mul_pow, hx₁3, hx₂3, one_mul]

theorem left_le_or_right_le (c : Cfg145 M X₁ X₂ P) {R : Subgroup K} (hRX : R ≤ X₁ ⊔ X₂)
    (hR : R ≠ ⊥) {d : K} (hd : d ∈ normalizer (R : Set K)) (hd₁ : ∀ x ∈ X₁, d * x * d⁻¹ = x⁻¹)
    (hd₂ : ∀ x ∈ X₂, d * x * d⁻¹ = x) : X₁ ≤ R ∨ X₂ ≤ R := by
  obtain ⟨r, hr1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hR
  have hrR : (r : K) ∈ R := r.2
  have hr1' : (r : K) ≠ 1 := fun h => hr1 (Subtype.ext h)
  have hcomm : ∀ x ∈ X₁, ∀ y ∈ X₂, x * y = y * x := by
    intro x hx y hy
    exact congrArg Subtype.val ((isElemAbelian c).1.is_comm.comm
      (⟨x, Subgroup.mem_sup_left hx⟩ : ↥(X₁ ⊔ X₂)) ⟨y, Subgroup.mem_sup_right hy⟩)
  have hset := (CFSG.GroupTheory.card_sup_mul_card_inf_of_commute X₁ X₂ hcomm).2
  obtain ⟨x₁, hx₁, x₂, hx₂, hr_eq⟩ :=
    Set.mem_mul.mp (by rw [← hset]; exact hRX hrR)
  have hdr : d * r * d⁻¹ ∈ R := (Subgroup.mem_normalizer_iff.mp hd r).mp hrR
  have hconj : d * r * d⁻¹ = x₁⁻¹ * x₂ := by
    rw [← hr_eq, ← MulAut.conj_apply, map_mul, MulAut.conj_apply, MulAut.conj_apply,
      hd₁ x₁ hx₁, hd₂ x₂ hx₂]
  have hx₁2R : x₁ ^ 2 ∈ R := by
    have hmem : r * (d * r * d⁻¹)⁻¹ ∈ R := R.mul_mem hrR (R.inv_mem hdr)
    rw [hconj, ← hr_eq] at hmem
    have hx : x₁ * x₂ * (x₁⁻¹ * x₂)⁻¹ = x₁ * x₁ := by group
    rw [hx] at hmem
    rwa [pow_two]
  by_cases hx₁1 : x₁ = 1
  · have hrx₂ : r = x₂ := by rw [← hr_eq, hx₁1, one_mul]
    have hx₂R : x₂ ∈ R := hrx₂ ▸ hrR
    have hx₂_ne : x₂ ≠ 1 := by rw [← hrx₂]; exact hr1'
    have hord₂ : orderOf x₂ = 3 := by
      have hdvd : orderOf x₂ ∣ 3 := by
        have h := Subgroup.orderOf_dvd_natCard X₂ hx₂
        rwa [c.card_right] at h
      rcases (Nat.dvd_prime Nat.prime_three).1 hdvd with h | h
      · exact absurd h (fun h1 => hx₂_ne (orderOf_eq_one_iff.mp h1))
      · exact h
    have hzp : Subgroup.zpowers x₂ = X₂ := by
      apply Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hx₂)
      rw [Nat.card_zpowers, hord₂, c.card_right]
    exact Or.inr (hzp ▸ Subgroup.zpowers_le.mpr hx₂R)
  · have hx₁2_ne : x₁ ^ 2 ≠ 1 := by
      intro h
      have h2 : orderOf x₁ ∣ 2 := orderOf_dvd_iff_pow_eq_one.mpr h
      have h3 : orderOf x₁ ∣ 3 := by
        have hh := Subgroup.orderOf_dvd_natCard X₁ hx₁
        rwa [c.card_left] at hh
      have hg : orderOf x₁ ∣ Nat.gcd 2 3 := Nat.dvd_gcd h2 h3
      rw [show Nat.gcd 2 3 = 1 by norm_num] at hg
      exact hx₁1 (orderOf_eq_one_iff.mp (Nat.dvd_one.mp hg))
    have hord₁2 : orderOf (x₁ ^ 2) = 3 := by
      have hdvd : orderOf (x₁ ^ 2) ∣ 3 := by
        have h := Subgroup.orderOf_dvd_natCard X₁ (X₁.pow_mem hx₁ 2)
        rwa [c.card_left] at h
      rcases (Nat.dvd_prime Nat.prime_three).1 hdvd with h | h
      · exact absurd h (fun h1 => hx₁2_ne (orderOf_eq_one_iff.mp h1))
      · exact h
    have hzp : Subgroup.zpowers (x₁ ^ 2) = X₁ := by
      apply Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr (X₁.pow_mem hx₁ 2))
      rw [Nat.card_zpowers, hord₁2, c.card_left]
    exact Or.inl (hzp ▸ Subgroup.zpowers_le.mpr hx₁2R)

theorem eq_left_or_eq_right (c : Cfg145 M X₁ X₂ P) {R : Subgroup K} (hRX : R ≤ X₁ ⊔ X₂)
    (hR : Nat.card R = 3) {d : K} (hd : d ∈ normalizer (R : Set K))
    (hd₁ : ∀ x ∈ X₁, d * x * d⁻¹ = x⁻¹) (hd₂ : ∀ x ∈ X₂, d * x * d⁻¹ = x) : R = X₁ ∨ R = X₂ := by
  have hRne : R ≠ ⊥ := by
    intro hbot
    rw [hbot] at hR
    norm_num at hR
  rcases left_le_or_right_le c hRX hRne hd hd₁ hd₂ with hX₁R | hX₂R
  · left
    exact (Subgroup.eq_of_le_of_card_ge hX₁R (by rw [hR, c.card_left])).symm
  · right
    exact (Subgroup.eq_of_le_of_card_ge hX₂R (by rw [hR, c.card_right])).symm

theorem eq_bot_of_normal_of_isPGroup (c : Cfg145 M X₁ X₂ P) {R : Subgroup K} (hR : R.Normal)
    (hR3 : IsPGroup 3 R) : R = ⊥ := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hcardX : Nat.card (X₁ ⊔ X₂ : Subgroup K) = 3 ^ (Nat.card K).factorization 3 := by
    have h := CFSG.ABGLocalTools.IsSylowOf.card_eq c.isSylowOf_three
    rwa [Subgroup.card_top] at h
  have hRX : R ≤ X₁ ⊔ X₂ := by
    have h := IsPGroup.le_sylow_of_normal hR3 (Sylow.ofCard (X₁ ⊔ X₂) hcardX)
    simpa using h
  by_contra hRne
  obtain ⟨d, -, hd₁, hd₂⟩ := c.inversion true false
  have hdR : d ∈ normalizer (R : Set K) := by
    rw [Subgroup.normalizer_eq_top_iff.mpr hR]
    exact Subgroup.mem_top d
  have hdvd9 : Nat.card R ∣ 3 ^ 2 := by
    have h : Nat.card R ∣ 9 := by
      rw [← c.card_sup]
      exact Subgroup.card_dvd_of_le hRX
    rwa [show (9 : ℕ) = 3 ^ 2 by norm_num] at h
  have hcard_cases : Nat.card R = 3 ∨ Nat.card R = 9 := by
    obtain ⟨k, hk, hk_eq⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 hdvd9
    have hne1 : Nat.card R ≠ 1 := fun h => hRne (Subgroup.card_eq_one.mp h)
    interval_cases k
    · simp only [pow_zero] at hk_eq
      exact absurd hk_eq hne1
    · left
      simpa using hk_eq
    · right
      simpa using hk_eq
  have hd₁' : ∀ x ∈ X₁, d * x * d⁻¹ = x⁻¹ := by simpa using hd₁
  have hd₂' : ∀ x ∈ X₂, d * x * d⁻¹ = x := by simpa using hd₂
  rcases left_le_or_right_le c hRX hRne hdR hd₁' hd₂' with hX₁R | hX₂R
  · rcases hcard_cases with h3 | h9
    · have hnorm : normalizer (X₁ : Set K) = ⊤ := by
        have hRtop : normalizer (R : Set K) = ⊤ := Subgroup.normalizer_eq_top_iff.mpr hR
        rw [Subgroup.eq_of_le_of_card_ge hX₁R (by rw [h3, c.card_left])]
        exact hRtop
      exact c.strong.1 (top_le_iff.mp (hnorm ▸ c.normalizer_left_le))
    · have hnorm : normalizer ((X₁ ⊔ X₂ : Subgroup K) : Set K) = ⊤ := by
        have hRtop : normalizer (R : Set K) = ⊤ := Subgroup.normalizer_eq_top_iff.mpr hR
        rw [(Subgroup.eq_of_le_of_card_ge hRX (by rw [h9, c.card_sup])).symm]
        exact hRtop
      exact c.strong.1 (top_le_iff.mp (hnorm ▸ c.normalizer_le))
  · rcases hcard_cases with h3 | h9
    · have hnorm : normalizer (X₂ : Set K) = ⊤ := by
        have hRtop : normalizer (R : Set K) = ⊤ := Subgroup.normalizer_eq_top_iff.mpr hR
        rw [Subgroup.eq_of_le_of_card_ge hX₂R (by rw [h3, c.card_right])]
        exact hRtop
      exact c.strong.1 (top_le_iff.mp (hnorm ▸ c.normalizer_right_le))
    · have hnorm : normalizer ((X₁ ⊔ X₂ : Subgroup K) : Set K) = ⊤ := by
        have hRtop : normalizer (R : Set K) = ⊤ := Subgroup.normalizer_eq_top_iff.mpr hR
        rw [(Subgroup.eq_of_le_of_card_ge hRX (by rw [h9, c.card_sup])).symm]
        exact hRtop
      exact c.strong.1 (top_le_iff.mp (hnorm ▸ c.normalizer_le))

theorem free (c : Cfg145 M X₁ X₂ P) : CFSG.ComponentClassification.SolvableRadical.Free K := by
  intro A hA hAsolv
  by_contra hAne
  obtain ⟨N, hNA, hNmin⟩ :=
    CFSG.ComponentClassification.MinimalNormal.exists_le A hAne
  haveI : Group.IsSolvable N :=
    Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hNA)
      (Subgroup.inclusion_injective hNA)
  obtain ⟨q, hq, -, hqP⟩ :=
    CFSG.ComponentClassification.MinimalNormal.elementaryAbelian_of_solvable N hNmin
  haveI : Fact q.Prime := ⟨hq⟩
  by_cases hq3 : q = 3
  · rw [hq3] at hqP
    exact hNmin.prop.2 (eq_bot_of_normal_of_isPGroup c hNmin.prop.1 hqP)
  · have h3N : ¬ 3 ∣ Nat.card N := by
      intro h3
      obtain ⟨k, hk⟩ := hqP.exists_card_eq
      rw [hk] at h3
      have h3q : 3 ∣ q := Nat.prime_three.dvd_of_dvd_pow h3
      rcases (Nat.dvd_prime hq).1 h3q with h | h
      · norm_num at h
      · exact hq3 h.symm
    exact hNmin.prop.2 (c.normal_eq_bot N hNmin.prop.1 h3N)

theorem false_of_le (c : Cfg145 M X₁ X₂ P) {E : Subgroup K} (hE : E.Normal) (hXE : X₁ ⊔ X₂ ≤ E)
    (hEM : E ≤ M) : False := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨Q, hQ⟩ := (c.isSylowOf_three.of_le hXE le_top).exists_sylow_eq_subgroupOf
  haveI : E.Normal := hE
  have hfr : normalizer ((X₁ ⊔ X₂ : Subgroup K) : Set K) ⊔ E = ⊤ := by
    have h := Sylow.normalizer_sup_eq_top Q
    rwa [hQ, Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hXE] at h
  have htopM : (⊤ : Subgroup K) ≤ M := hfr ▸ sup_le c.normalizer_le hEM
  exact c.strong.1 (top_le_iff.mp htopM)

end Cfg145

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
