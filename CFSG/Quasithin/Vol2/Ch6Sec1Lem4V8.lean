module

public import CFSG.Quasithin.Vol2.Ch6Sec1Lem4V2
public import CFSG.Quasithin.Vol2.Ch6Sec1Lem4VIn

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin

variable {Γ : Type} [Group Γ] [Finite Γ]

theorem le_normalizer_or_le_of_five614 {H K T X : Subgroup Γ} (hyp : Five614Hyp H K T X) :
    X ≤ Subgroup.normalizer ((T ⊓ K : Subgroup Γ) : Set Γ) ∨ X ≤ K := by
  classical
  obtain ⟨-, -, -, -, hT2, -, -, -, hXO, hX5, hXn, hTX, hXK, -, -⟩ := hyp
  set P := X ⊓ T with hP
  have hP2 : IsPGroup 2 P := hT2.to_le inf_le_right
  have hTXx : ∀ t ∈ T, ∀ x ∈ X, t * x * t⁻¹ ∈ X := fun t ht x hx =>
    (Subgroup.mem_normalizer_iff.mp (hTX ht) x).mp hx
  have hTP : ∀ t ∈ T, ∀ p ∈ P, t * p * t⁻¹ ∈ P := fun t ht p hp =>
    ⟨hTXx t ht p hp.1, T.mul_mem (T.mul_mem ht hp.2) (T.inv_mem ht)⟩
  by_cases htriv : ∀ s ∈ T ⊓ K, ∀ x ∈ X, s * x * s⁻¹ * x⁻¹ ∈ P
  ·
    left
    intro x hx
    have hle : (T ⊓ K).map (MulAut.conj x).toMonoidHom ≤ T ⊓ K := by
      rintro _ ⟨s, hs, rfl⟩
      have h1 := htriv s hs x hx
      refine ⟨?_, (Subgroup.mem_normalizer_iff.mp (hXK hx) s).mp hs.2⟩
      have h2 : (s * x * s⁻¹ * x⁻¹)⁻¹ ∈ T := T.inv_mem h1.2
      have e : (MulAut.conj x).toMonoidHom s = (s * x * s⁻¹ * x⁻¹)⁻¹ * s := by
        simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
        group
      rw [e]
      exact T.mul_mem h2 hs.1
    exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr (Subgroup.eq_of_le_of_card_ge hle
      (by rw [Subgroup.card_map_of_injective (MulAut.conj x).injective]))
  ·
    right
    push Not at htriv
    obtain ⟨s, hs, x₁, hx₁, hns⟩ := htriv
    set P' : Subgroup ↥X := P.subgroupOf X with hP'
    have : P'.Normal := hXn
    have hQ5 : Nat.card (↥X ⧸ P') = 5 := hX5
    have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
    have : IsCyclic (↥X ⧸ P') := isCyclic_of_prime_card hQ5
    have hg5 : ∀ g : ↥X ⧸ P', g ^ 5 = 1 := fun g => by
      rw [← hQ5]
      exact pow_card_eq_one'
    let cX : ∀ t ∈ T, ↥X →* ↥X := fun t ht =>
      { toFun := fun x => ⟨t * x * t⁻¹, hTXx t ht x x.2⟩
        map_one' := Subtype.ext (by simp)
        map_mul' := fun a b => Subtype.ext (by simp [mul_assoc]) }
    have hcX : ∀ t (ht : t ∈ T), P' ≤ P'.comap (cX t ht) := fun t ht p hp =>
      hTP t ht p hp
    let φ : ∀ t ∈ T, (↥X ⧸ P') →* (↥X ⧸ P') := fun t ht =>
      QuotientGroup.map P' P' (cX t ht) (hcX t ht)
    have hφ : ∀ t (ht : t ∈ T) (x : ↥X),
        φ t ht (x : ↥X ⧸ P') = ((⟨t * x * t⁻¹, hTXx t ht x x.2⟩ : ↥X) : ↥X ⧸ P') :=
      fun _ _ _ => rfl
    have hinv : ∀ t (ht : t ∈ T), (∀ g, φ t ht g = g⁻¹) → ∀ x ∈ X, x * (t * x * t⁻¹) ∈ P := by
      intro t ht h x hx
      have h1 := h (⟨x, hx⟩ : ↥X)
      rw [hφ t ht ⟨x, hx⟩] at h1
      have h2 : ((⟨x, hx⟩ * ⟨t * x * t⁻¹, hTXx t ht x hx⟩ : ↥X) : ↥X ⧸ P') = 1 := by
        rw [QuotientGroup.mk_mul]
        show ((⟨x, hx⟩ : ↥X) : ↥X ⧸ P') * ((⟨t * x * t⁻¹, hTXx t ht x hx⟩ : ↥X) : ↥X ⧸ P') = 1
        rw [h1, mul_inv_cancel]
      exact (QuotientGroup.eq_one_iff (N := P') _).mp h2
    have hsT : s ∈ T := hs.1
    obtain ⟨m, hm⟩ := MonoidHom.map_cyclic (φ s hsT)
    have hmod : ∀ g : ↥X ⧸ P', g ^ m = g ^ (m % 5) := fun g => by
      conv_lhs => rw [← Int.mul_ediv_add_emod m 5]
      have h5 : g ^ (5 : ℤ) = 1 := by
        rw [show (5 : ℤ) = ((5 : ℕ) : ℤ) by norm_num, zpow_natCast]
        exact hg5 g
      rw [zpow_add, zpow_mul, h5, one_zpow, one_mul]
    have hr0 : 0 ≤ m % 5 := Int.emod_nonneg m (by norm_num)
    have hr5 : m % 5 < 5 := Int.emod_lt_of_pos m (by norm_num)
    have hφr : ∀ g, φ s hsT g = g ^ (m % 5) := fun g => by rw [hm, hmod]
    have hpow : ∀ (g : ↥X ⧸ P') (k : ℕ), g ^ k = g ^ (k % 5) := fun g k => by
      conv_lhs => rw [← Nat.div_add_mod k 5]
      rw [pow_add, pow_mul, hg5, one_pow, one_mul]
    have hss : s * s ∈ T := T.mul_mem hsT hsT
    have hφss : ∀ g, φ (s * s) hss g = φ s hsT (φ s hsT g) := by
      intro g
      induction g using QuotientGroup.induction_on with
      | H x =>
        rw [hφ (s * s) hss x, hφ s hsT x, hφ s hsT _]
        congr 1
        apply Subtype.ext
        show s * s * (x : Γ) * (s * s)⁻¹ = s * (s * x * s⁻¹) * s⁻¹
        group
    have hx₁P : x₁ ∉ P := fun h1 => hns (P.mul_mem (hTP s hsT x₁ h1) (P.inv_mem h1))
    have hns' : φ s hsT (⟨x₁, hx₁⟩ : ↥X) ≠ ((⟨x₁, hx₁⟩ : ↥X) : ↥X ⧸ P') := by
      intro h1
      rw [hφ s hsT ⟨x₁, hx₁⟩, QuotientGroup.eq] at h1
      apply hns
      have h2 : ((⟨s * x₁ * s⁻¹, hTXx s hsT x₁ hx₁⟩ : ↥X)⁻¹ * ⟨x₁, hx₁⟩ : ↥X) ∈ P' := h1
      have h3 := P'.inv_mem ((inferInstance : P'.Normal).conj_mem _ h2 ⟨x₁, hx₁⟩)
      have h4 : (((⟨x₁, hx₁⟩ * ((⟨s * x₁ * s⁻¹, hTXx s hsT x₁ hx₁⟩ : ↥X)⁻¹ * ⟨x₁, hx₁⟩) *
          (⟨x₁, hx₁⟩ : ↥X)⁻¹)⁻¹ : ↥X) : Γ) ∈ P := h3
      simp only [Subgroup.coe_mul, Subgroup.coe_inv] at h4
      convert h4 using 1
      group
    have hx₁1 : ((⟨x₁, hx₁⟩ : ↥X) : ↥X ⧸ P') ≠ 1 := by
      intro h1
      exact hx₁P ((QuotientGroup.eq_one_iff (N := P') _).mp h1)
    obtain ⟨t, ht, htinv⟩ : ∃ t, ∃ ht : t ∈ T ⊓ K, ∀ g, φ t ht.1 g = g⁻¹ := by
      generalize hr : m % 5 = r at hφr hr0 hr5
      have hginv : ∀ g : ↥X ⧸ P', g ^ (4 : ℕ) = g⁻¹ := fun g => by
        rw [eq_inv_iff_mul_eq_one, ← pow_succ]
        exact hg5 g
      interval_cases r
      · exfalso
        apply hx₁1
        have h1 := hφr (⟨x₁, hx₁⟩ : ↥X)
        rw [zpow_zero, hφ s hsT ⟨x₁, hx₁⟩] at h1
        have h2 : s * x₁ * s⁻¹ ∈ P := (QuotientGroup.eq_one_iff (N := P') _).mp h1
        refine (QuotientGroup.eq_one_iff (N := P') _).mpr (Subgroup.mem_subgroupOf.mpr ?_)
        have := hTP s⁻¹ (T.inv_mem hsT) _ h2
        simpa [mul_assoc] using this
      · exfalso
        exact hns' (by rw [hφr, zpow_one])
      · refine ⟨s * s, ⟨hss, K.mul_mem hs.2 hs.2⟩, fun g => ?_⟩
        rw [hφss, hφr, hφr, ← zpow_mul]
        norm_num
        rw [hginv]
      · refine ⟨s * s, ⟨hss, K.mul_mem hs.2 hs.2⟩, fun g => ?_⟩
        rw [hφss, hφr, hφr, ← zpow_mul]
        norm_num
        rw [hpow, hginv]
      · refine ⟨s, hs, fun g => ?_⟩
        rw [hφr]
        norm_num
        rw [hginv]
    exact le_of_mul_conj_mem614 hXK hP2 hXO ht.2 (hinv t ht.1 htinv)

theorem kg614FiveL3_holds : KG614FiveL3 := by
  intro Γ _ _ H K T X hyp hL3
  obtain ⟨p, hp, hp2, hmod⟩ := hL3
  rcases le_normalizer_or_le_of_five614 hyp with hN | hXK
  · exact Or.inl hN
  · refine Or.inr (Or.inl ⟨hXK, Or.inr ?_⟩)
    rcases hmod with h | h
    · exact ⟨true, p, hp, hp2, h⟩
    · exact ⟨false, p, hp, hp2, h⟩

end CFSG.Quasithin.H13
