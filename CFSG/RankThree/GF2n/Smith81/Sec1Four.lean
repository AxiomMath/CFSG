module

public import CFSG.RankThree.GF2n.Smith81.Sec1Frobenius

public section

namespace CFSG.RankThree.GF2n.Smith81

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
  CFSG.RankThree.GF2n CFSG.RankThree.GF2n.Stroth80
open scoped commutatorElement

variable {G : Type} [Group G]

section Klein

variable [Finite G] {Y : Subgroup G} {m : G}

theorem klein_fixed (hY : Nat.card Y = 4) (hY2 : ∀ y ∈ Y, y * y = 1)
    (hYc : ∀ a ∈ Y, ∀ b ∈ Y, a * b = b * a) (hN : ∀ y ∈ Y, m * y * m⁻¹ ∈ Y) (hm2 : m * m = 1)
    {u : G} (hu : u ∈ Y) (hmu : m * u * m⁻¹ ≠ u) :
    u * (m * u * m⁻¹) ≠ 1 ∧ m * (u * (m * u * m⁻¹)) * m⁻¹ = u * (m * u * m⁻¹) ∧
      ∀ y ∈ Y, m * y * m⁻¹ = y → y = 1 ∨ y = u * (m * u * m⁻¹) := by
  have hminv : m⁻¹ = m := inv_eq_of_mul_eq_one_right hm2
  have hu' : m * u * m⁻¹ ∈ Y := hN u hu
  have huinv : u⁻¹ = u := inv_eq_of_mul_eq_one_right (hY2 u hu)
  have hy₀Y : u * (m * u * m⁻¹) ∈ Y := Y.mul_mem hu hu'
  have hy₀1 : u * (m * u * m⁻¹) ≠ 1 := by
    intro h
    apply hmu
    have h1 : m * u * m⁻¹ = u⁻¹ := eq_inv_of_mul_eq_one_right h
    rw [h1, huinv]
  have hfix : m * (u * (m * u * m⁻¹)) * m⁻¹ = u * (m * u * m⁻¹) := by
    have e : m * (u * (m * u * m⁻¹)) * m⁻¹ = (m * u * m⁻¹) * ((m * m) * u * (m * m)⁻¹) := by
      group
    rw [e, hm2]
    simp only [inv_one, mul_one, one_mul]
    exact hYc _ hu' _ hu
  refine ⟨hy₀1, hfix, ?_⟩
  set F : Subgroup G := Y ⊓ Subgroup.centralizer ({m} : Set G) with hF
  have hmem : ∀ y, y ∈ F ↔ y ∈ Y ∧ m * y * m⁻¹ = y := by
    intro y
    rw [hF, Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff]
    constructor
    · rintro ⟨hy, h⟩
      exact ⟨hy, by rw [← h]; group⟩
    · rintro ⟨hy, h⟩
      refine ⟨hy, ?_⟩
      calc y * m = (m * y * m⁻¹) * m := by rw [h]
        _ = m * y := by group
  have hFY : F ≤ Y := inf_le_left
  have hdvd : Nat.card F ∣ 4 := hY ▸ Subgroup.card_dvd_of_le hFY
  have hFne : Nat.card F ≠ 4 := by
    intro h4
    have hEq : F = Y := Subgroup.eq_of_le_of_card_ge hFY (by rw [hY, h4])
    exact hmu ((hmem u).mp (hEq ▸ hu)).2
  have hF2 : Nat.card F ≤ 2 := by
    obtain ⟨i, hi, hc⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (by simpa using hdvd :
      Nat.card F ∣ 2 ^ 2)
    interval_cases i
    · simp [hc]
    · simp [hc]
    · exact absurd (by simpa using hc) hFne
  intro y hy hmy
  by_contra hcon
  push Not at hcon
  have h3 : 2 < (F : Set G).ncard := by
    rw [Set.two_lt_ncard_iff]
    exact ⟨1, u * (m * u * m⁻¹), y, F.one_mem, (hmem _).mpr ⟨hy₀Y, hfix⟩, (hmem y).mpr ⟨hy, hmy⟩,
      hy₀1.symm, hcon.1.symm, hcon.2.symm⟩
  have h4 : Nat.card F = (F : Set G).ncard := Nat.card_coe_set_eq (F : Set G)
  omega

theorem klein_no_sqrt (hY : Nat.card Y = 4) (hY2 : ∀ y ∈ Y, y * y = 1)
    (hYc : ∀ a ∈ Y, ∀ b ∈ Y, a * b = b * a) (hN : ∀ y ∈ Y, m * y * m⁻¹ ∈ Y) (hm2 : m * m = 1)
    {u : G} (hu : u ∈ Y) (hmu : m * u * m⁻¹ ≠ u) {ρ : G}
    (hρN : ∀ y ∈ Y, ρ * y * ρ⁻¹ ∈ Y) (hρρ : ρ * ρ = m) : False := by
  obtain ⟨hy₀1, hfix, hset⟩ := klein_fixed hY hY2 hYc hN hm2 hu hmu
  have hu' : m * u * m⁻¹ ∈ Y := hN u hu
  have hy₀Y : u * (m * u * m⁻¹) ∈ Y := Y.mul_mem hu hu'
  have hcomm : ∀ y, m * (ρ * y * ρ⁻¹) * m⁻¹ = ρ * (m * y * m⁻¹) * ρ⁻¹ := by
    intro y
    rw [← hρρ]
    group
  have hρinj : ∀ y, ρ * y * ρ⁻¹ = 1 → y = 1 := by
    intro y h
    have : y = ρ⁻¹ * (ρ * y * ρ⁻¹) * ρ := by group
    rw [this, h]
    group
  have hσy₀ : ρ * (u * (m * u * m⁻¹)) * ρ⁻¹ = u * (m * u * m⁻¹) := by
    have h1 : m * (ρ * (u * (m * u * m⁻¹)) * ρ⁻¹) * m⁻¹ = ρ * (u * (m * u * m⁻¹)) * ρ⁻¹ := by
      rw [hcomm, hfix]
    rcases hset _ (hρN _ hy₀Y) h1 with h | h
    · exact absurd (hρinj _ h) hy₀1
    · exact h
  have hb : (ρ * u * ρ⁻¹) * (m * (ρ * u * ρ⁻¹) * m⁻¹) = u * (m * u * m⁻¹) := by
    calc (ρ * u * ρ⁻¹) * (m * (ρ * u * ρ⁻¹) * m⁻¹)
        = (ρ * u * ρ⁻¹) * (ρ * (m * u * m⁻¹) * ρ⁻¹) := by rw [hcomm]
      _ = ρ * (u * (m * u * m⁻¹)) * ρ⁻¹ := by group
      _ = u * (m * u * m⁻¹) := hσy₀
  have hbY : ρ * u * ρ⁻¹ ∈ Y := hρN u hu
  have hbb : (ρ * u * ρ⁻¹) * (ρ * u * ρ⁻¹) = 1 := by
    have : (ρ * u * ρ⁻¹) * (ρ * u * ρ⁻¹) = ρ * (u * u) * ρ⁻¹ := by group
    rw [this, hY2 u hu]
    group
  have huu : u * u = 1 := hY2 u hu
  have hu'u' : (m * u * m⁻¹) * (m * u * m⁻¹) = 1 := by
    have : (m * u * m⁻¹) * (m * u * m⁻¹) = m * (u * u) * m⁻¹ := by group
    rw [this, huu]
    group
  have hbinv : (ρ * u * ρ⁻¹)⁻¹ = ρ * u * ρ⁻¹ := inv_eq_of_mul_eq_one_right hbb
  have hcb : m * (ρ * u * ρ⁻¹) * m⁻¹ = (ρ * u * ρ⁻¹) * (u * (m * u * m⁻¹)) := by
    have h1 := hb
    have : m * (ρ * u * ρ⁻¹) * m⁻¹ = (ρ * u * ρ⁻¹)⁻¹ * (u * (m * u * m⁻¹)) := by
      rw [← h1]
      group
    rw [this, hbinv]
  have hbu : m * ((ρ * u * ρ⁻¹) * u) * m⁻¹ = (ρ * u * ρ⁻¹) * u := by
    have e : m * ((ρ * u * ρ⁻¹) * u) * m⁻¹ =
        (m * (ρ * u * ρ⁻¹) * m⁻¹) * (m * u * m⁻¹) := by group
    rw [e, hcb]
    calc (ρ * u * ρ⁻¹) * (u * (m * u * m⁻¹)) * (m * u * m⁻¹)
        = (ρ * u * ρ⁻¹) * u * ((m * u * m⁻¹) * (m * u * m⁻¹)) := by group
      _ = (ρ * u * ρ⁻¹) * u := by rw [hu'u', mul_one]
  have hbuY : (ρ * u * ρ⁻¹) * u ∈ Y := Y.mul_mem hbY hu
  have hρρu : ρ * (ρ * u * ρ⁻¹) * ρ⁻¹ = u := by
    rcases hset _ hbuY hbu with h | h
    ·
      have hb1 : ρ * u * ρ⁻¹ = u := by
        have h1 : ρ * u * ρ⁻¹ = u⁻¹ := eq_inv_of_mul_eq_one_left h
        rw [h1, inv_eq_of_mul_eq_one_right huu]
      rw [hb1, hb1]
    ·
      have hb2 : ρ * u * ρ⁻¹ = m * u * m⁻¹ := by
        have h1 : ρ * u * ρ⁻¹ = (u * (m * u * m⁻¹)) * u⁻¹ := eq_mul_inv_of_mul_eq h
        rw [h1, inv_eq_of_mul_eq_one_right huu]
        calc u * (m * u * m⁻¹) * u = u * ((m * u * m⁻¹) * u) := by group
          _ = u * (u * (m * u * m⁻¹)) := by rw [hYc _ hu' _ hu]
          _ = (u * u) * (m * u * m⁻¹) := by group
          _ = m * u * m⁻¹ := by rw [huu, one_mul]
      rw [hb2, ← hcomm u, hb2]
      calc m * (m * u * m⁻¹) * m⁻¹ = (m * m) * u * (m * m)⁻¹ := by group
        _ = u := by rw [hm2]; group
  apply hmu
  calc m * u * m⁻¹ = ρ * (ρ * u * ρ⁻¹) * ρ⁻¹ := by rw [← hρρ]; group
    _ = u := hρρu

end Klein

section Model

variable [Finite G] {M Q Z : Subgroup G}

theorem exists_mem_Q_not_mem_Z (H : StrothHyp M Q Z) : ∃ q ∈ Q, q ∉ Z := by
  obtain ⟨g, hgV, hgQ⟩ := H.toHyp79.exists_opposite
  have hbot := inf_conjSubgroup_eq_bot_of_isTI H.toHyp79.ti hgV
  have hne : conjSubgroup g Z ≠ ⊥ := by
    intro h
    have h1 : Nat.card (conjSubgroup g Z) = Nat.card Z := card_conjSubgroup g Z
    rw [h, Subgroup.card_bot] at h1
    have := H.q4
    omega
  obtain ⟨⟨b, hb⟩, hb1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hne
  refine ⟨b, hgQ hb, fun hbZ => ?_⟩
  have : b ∈ Z ⊓ conjSubgroup g Z := ⟨hbZ, hb⟩
  rw [hbot, Subgroup.mem_bot] at this
  exact hb1 (Subtype.ext this)

theorem exists_fixed_sq (H : StrothHyp M Q Z) {x : G} (hxM : x ∈ M) (hx2 : x * x = 1)
    (hnt : ∃ z ∈ Z, x * z * x⁻¹ ≠ z) {z₀ u : G} (hz₀ : z₀ ∈ Z) (hz₀1 : z₀ ≠ 1)
    (hset : ∀ y ∈ Z, x * y * x⁻¹ = y → y = 1 ∨ y = z₀) (huZ : u ∈ Z)
    (hu : u * (x * u * x⁻¹) = z₀) : ∃ q ∈ Q, x * q * x⁻¹ = q ∧ q * q = z₀ := by
  obtain ⟨K, _, _, hch, γ, M₀, hD⟩ := stroth_globalModelData H
  obtain ⟨σ, a, T, hT1, hTπ, hTγ, hTQ⟩ := hD.act x hxM
  have h2K : (2 : K) = 0 := CharP.cast_eq_zero K 2
  have hxN : ∀ z ∈ Z, x * z * x⁻¹ ∈ Z := fun z hz =>
    (Subgroup.mem_normalizer_iff.mp (H.Z_normal.2 hxM) z).mp hz
  have hxx : ∀ y : G, x * (x * y * x⁻¹) * x⁻¹ = y := by
    intro y
    calc x * (x * y * x⁻¹) * x⁻¹ = (x * x) * y * (x * x)⁻¹ := by group
      _ = y := by rw [hx2]; group
  have hσ : ∃ c : K, σ c ≠ c := by
    by_contra hcon
    push Not at hcon
    obtain ⟨z₁, hz₁Z, hz₁⟩ := hD.reg.surj 1
    have h1 : γ (x * z₁ * x⁻¹) = a := by rw [hTγ z₁ hz₁Z, hz₁, hcon, mul_one]
    have h2 : γ (x * (x * z₁ * x⁻¹) * x⁻¹) = (a : K) * (a : K) := by
      rw [hTγ _ (hxN z₁ hz₁Z), h1, hcon]
    rw [hxx, hz₁] at h2
    have ha1 : (a : K) = 1 := by
      have : ((a : K) - 1) ^ 2 = 0 := by linear_combination -h2 + (1 - (a : K)) * h2K
      exact sub_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp this)
    obtain ⟨z, hzZ, hz⟩ := hnt
    apply hz
    refine GM.eq_of_γ_eq hD (hxN z hzZ) hzZ ?_
    rw [hTγ z hzZ, hcon, ha1, one_mul]
  obtain ⟨c, hc⟩ := hσ
  have hTT : ∀ e, T (T e) = e := by
    intro e
    obtain ⟨y, hy, rfl⟩ := M₀.π_surj e
    rw [← hTπ y hy, ← hTπ _ (conj_mem_Q H hxM hy), hxx]
  have hex : ∃ e, T e = e ∧ M₀.Qf e ≠ 0 := by
    by_contra hcon
    push Not at hcon
    have hBfix : ∀ f f', T f = f → T f' = f' → M₀.B f f' = 0 := by
      intro f f' hf hf'
      have h1 := M₀.Qf_add f f'
      have hff' : T (f + f') = f + f' := by rw [map_add, hf, hf']
      rw [hcon _ hff', hcon f hf, hcon f' hf'] at h1
      linear_combination -h1
    have ht : σ c + c ≠ 0 := by
      intro h
      apply hc
      linear_combination h - c * h2K
    have hspan : ∀ e : M₀.E, ∃ f₁ f₂ : M₀.E, T f₁ = f₁ ∧ T f₂ = f₂ ∧
        (σ c + c) • e = σ c • f₁ + f₂ := by
      intro e
      refine ⟨e + T e, c • e + T (c • e), ?_, ?_, ?_⟩
      · rw [map_add, hTT, add_comm]
      · rw [map_add, hTT, add_comm]
      · rw [hT1 c e]
        have h2 : (σ c + σ c) • T e = 0 := by
          rw [← two_mul, h2K, zero_mul, zero_smul]
        calc (σ c + c) • e = σ c • (e + T e) + (c • e + σ c • T e) - (σ c + σ c) • T e := by
              module
          _ = σ c • (e + T e) + (c • e + σ c • T e) := by rw [h2, sub_zero]
    have hB0 : ∀ e e' : M₀.E, M₀.B e e' = 0 := by
      intro e e'
      obtain ⟨f₁, f₂, hf₁, hf₂, he⟩ := hspan e
      obtain ⟨f₁', f₂', hf₁', hf₂', he'⟩ := hspan e'
      have h1 : M₀.B ((σ c + c) • e) ((σ c + c) • e') = 0 := by
        rw [he, he']
        simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul,
          hBfix f₁ f₁' hf₁ hf₁', hBfix f₁ f₂' hf₁ hf₂', hBfix f₂ f₁' hf₂ hf₁',
          hBfix f₂ f₂' hf₂ hf₂', mul_zero, add_zero]
      simp only [map_smul, LinearMap.smul_apply, smul_eq_mul] at h1
      have h3 : (σ c + c) * ((σ c + c) * M₀.B e e') = 0 := h1
      rcases mul_eq_zero.mp h3 with h | h
      · exact absurd h ht
      · rcases mul_eq_zero.mp h with h | h
        · exact absurd h ht
        · exact h
    obtain ⟨q, hq, hqZ⟩ := exists_mem_Q_not_mem_Z H
    exact hqZ ((M₀.π_ker q hq).mp (M₀.nondeg _ fun f => hB0 _ f))
  obtain ⟨e₁, he₁, hQ₁⟩ := hex
  obtain ⟨z_e, hz_eZ, hz_e⟩ := hD.reg.surj (M₀.Qf e₁)
  have hz_efix : x * z_e * x⁻¹ = z_e := by
    refine GM.eq_of_γ_eq hD (hxN z_e hz_eZ) hz_eZ ?_
    rw [hTγ z_e hz_eZ, hz_e, ← hTQ e₁, he₁]
  have hz_e1 : z_e ≠ 1 := by
    intro h
    apply hQ₁
    rw [← hz_e, h]
    exact hD.reg.one
  have hz_e0 : z_e = z₀ := (hset z_e hz_eZ hz_efix).resolve_left hz_e1
  obtain ⟨q, hq, hπq⟩ := M₀.π_surj e₁
  have hqq : q * q = z₀ := by
    rw [← hz_e0, ← pow_two]
    refine GM.eq_of_γ_eq hD (sq_mem_Z H hq) hz_eZ ?_
    rw [M₀.sq_eq q hq, hπq, hz_e]
  have hyQ : x * q * x⁻¹ ∈ Q := conj_mem_Q H hxM hq
  have hπy : M₀.π (x * q * x⁻¹) = M₀.π q := by rw [hTπ q hq, hπq, he₁]
  have hw₀Q : q⁻¹ * (x * q * x⁻¹) ∈ Q := Q.mul_mem (Q.inv_mem hq) hyQ
  have hw₀Z : q⁻¹ * (x * q * x⁻¹) ∈ Z := by
    refine (M₀.π_ker _ hw₀Q).mp ?_
    rw [M₀.π_mul _ (Q.inv_mem hq) _ hyQ, Tim79.QuadModel.pi_inv M₀ hq, hπy]
    exact neg_add_cancel _
  set w₀ := q⁻¹ * (x * q * x⁻¹) with hw₀
  have hw₀fix : x * w₀ * x⁻¹ = w₀ := by
    have hsq : w₀ * w₀ = 1 := by rw [← pow_two]; exact Z_sq H hw₀Z
    have h1 : x * w₀ * x⁻¹ = w₀⁻¹ := by
      rw [hw₀]
      calc x * (q⁻¹ * (x * q * x⁻¹)) * x⁻¹ = (x * q * x⁻¹)⁻¹ * (x * (x * q * x⁻¹) * x⁻¹) := by
            group
        _ = (q⁻¹ * (x * q * x⁻¹))⁻¹ := by rw [hxx]; group
    rw [h1, inv_eq_of_mul_eq_one_right hsq]
  rcases hset w₀ hw₀Z hw₀fix with h | h
  · refine ⟨q, hq, ?_, hqq⟩
    have : x * q * x⁻¹ = q * w₀ := by rw [hw₀]; group
    rw [this, h, mul_one]
  · have huQ : u ∈ Q := H.Z_normal.1 huZ
    refine ⟨q * u, Q.mul_mem hq huQ, ?_, ?_⟩
    · have h1 : x * q * x⁻¹ = q * z₀ := by
        have : x * q * x⁻¹ = q * w₀ := by rw [hw₀]; group
        rw [this, h]
      have hxu : (x * u * x⁻¹) * (x * u * x⁻¹) = 1 := by
        have : (x * u * x⁻¹) * (x * u * x⁻¹) = x * (u * u) * x⁻¹ := by group
        rw [this, ← pow_two, Z_sq H huZ]
        group
      have h2 : z₀ * (x * u * x⁻¹) = u := by
        rw [← hu]
        calc u * (x * u * x⁻¹) * (x * u * x⁻¹) = u * ((x * u * x⁻¹) * (x * u * x⁻¹)) := by group
          _ = u := by rw [hxu, mul_one]
      calc x * (q * u) * x⁻¹ = (x * q * x⁻¹) * (x * u * x⁻¹) := by group
        _ = q * (z₀ * (x * u * x⁻¹)) := by rw [h1]; group
        _ = q * u := by rw [h2]
    · have huz : u * q = q * u := Z_central H huZ hq
      have hu2 : u * u = 1 := by rw [← pow_two]; exact Z_sq H huZ
      calc q * u * (q * u) = q * (u * q) * u := by group
        _ = q * (q * u) * u := by rw [huz]
        _ = (q * q) * (u * u) := by group
        _ = z₀ := by rw [hqq, hu2, mul_one]

end Model

section Four

variable [Finite G] {M Q Z X : Subgroup G} {x : G}

theorem smith_1_12_four (hs : Sit M Q Z X x) (h4 : Nat.card Z = 4) :
    Post12 M Q Z X := by
  have H := hs.hyp
  have hZQ := H.Z_normal.1
  have hXQ := hs.X_inf_Q
  have hx2 := hs.x_sq
  obtain ⟨g, hg, -, -⟩ := hs.QB_eq
  have hZc : ∀ a ∈ Z, ∀ b ∈ Z, a * b = b * a := fun a ha b hb => Z_central H ha (hZQ hb)
  have hZ2 : ∀ z ∈ Z, z * z = 1 := fun z hz => by rw [← pow_two]; exact Z_sq H hz
  have hXcard : Nat.card X = 4 := by rw [hg, card_conjSubgroup g Z, h4]
  have hxN : ∀ z ∈ Z, x * z * x⁻¹ ∈ Z := fun z hz =>
    (Subgroup.mem_normalizer_iff.mp (H.Z_normal.2 hs.memM) z).mp hz
  by_cases hcent : ∃ w ∈ X, w ≠ 1 ∧ w ∈ Subgroup.centralizer (Z : Set G)
  · obtain ⟨w₀, hw₀X, hw₀1, hw₀C⟩ := hcent
    have hZN : ∀ z ∈ Z, z ∈ Subgroup.normalizer (X : Set G) := fun z hz =>
      Tim77.mem_normalizer_of_commute_of_isTI hs.X_isTI hw₀X hw₀1
        (Subgroup.mem_centralizer_iff.mp hw₀C z hz)
    exact hs.post12_of_Z_le_normalizer hXQ
      (hs.X_le_M_of_Z_le_normalizer (by omega) hZN) hZN
  · exfalso
    push Not at hcent
    have hxnt : ∃ z ∈ Z, x * z * x⁻¹ ≠ z := by
      by_contra hcon
      push Not at hcon
      refine hcent x hs.mem hs.ne_one (Subgroup.mem_centralizer_iff.mpr fun z hz => ?_)
      have := hcon z hz
      calc z * x = (x * z * x⁻¹) * x := by rw [this]
        _ = x * z := by group
    obtain ⟨z₁, hz₁Z, hz₁ne⟩ := hxnt
    obtain ⟨hz₀1, hz₀fix, hset⟩ := klein_fixed (Y := Z) (m := x) h4 hZ2 hZc hxN hx2 hz₁Z hz₁ne
    set z₀ := z₁ * (x * z₁ * x⁻¹) with hz₀def
    have hz₀Z : z₀ ∈ Z := Z.mul_mem hz₁Z (hxN z₁ hz₁Z)
    have hz₀x : z₀ * x = x * z₀ := by
      calc z₀ * x = (x * z₀ * x⁻¹) * x := by rw [hz₀fix]
        _ = x * z₀ := by group
    have hz₀N : z₀ ∈ Subgroup.normalizer (X : Set G) :=
      Tim77.mem_normalizer_of_commute_of_isTI hs.X_isTI hs.mem hs.ne_one hz₀x
    have hz₀N' : ∀ y ∈ X, z₀ * y * z₀⁻¹ ∈ X := fun y hy =>
      (Subgroup.mem_normalizer_iff.mp hz₀N y).mp hy
    have hz₀nt : ∃ w ∈ X, z₀ * w * z₀⁻¹ ≠ w := by
      by_contra hcon
      push Not at hcon
      have hXM : ∀ w ∈ X, w ∈ M := hs.X_le_M_of_centralizes hz₀Z hz₀1
        (Subgroup.mem_centralizer_iff.mpr fun w hw => by
          have := hcon w hw
          calc w * z₀ = (z₀ * w * z₀⁻¹) * z₀ := by rw [this]
            _ = z₀ * w := by group)
      have hcover := semilin_cover (semilinAct_Z H) hZ2 (C := X) (fun w hw => hXM w hw)
        hs.X_sq hs.X_comm
      have hbot : X ⊓ Subgroup.centralizer (Z : Set G) = ⊥ := by
        rw [eq_bot_iff]
        intro w hw
        obtain ⟨hwX, hwC⟩ := Subgroup.mem_inf.mp hw
        by_contra hw1
        exact hcent w hwX (fun h => hw1 (by rw [h]; exact Subgroup.one_mem _)) hwC
      rw [hbot, Subgroup.card_bot] at hcover
      omega
    obtain ⟨w₁, hw₁X, hw₁ne⟩ := hz₀nt
    obtain ⟨-, -, hxset⟩ := klein_fixed (Y := X) (m := z₀) hXcard hs.X_sq hs.X_comm hz₀N'
      (hZ2 z₀ hz₀Z) hw₁X hw₁ne
    have hxeq : x = w₁ * (z₀ * w₁ * z₀⁻¹) := by
      refine (hxset x hs.mem ?_).resolve_left hs.ne_one
      calc z₀ * x * z₀⁻¹ = (x * z₀) * z₀⁻¹ := by rw [hz₀x]
        _ = x := by group
    have hz₁inv : z₁⁻¹ = z₁ := inv_eq_of_mul_eq_one_right (hZ2 z₁ hz₁Z)
    have hw₁inv : w₁⁻¹ = w₁ := inv_eq_of_mul_eq_one_right (hs.X_sq w₁ hw₁X)
    have hR1 : z₁ * x * z₁⁻¹ = z₀ * x := by
      rw [hz₀def, hz₁inv]
      group
    have hR2 : w₁ * z₀ * w₁⁻¹ = x * z₀ := by
      conv_rhs => rw [hxeq]
      rw [hw₁inv]
      group
    have hR3 : z₁ * z₀ * z₁⁻¹ = z₀ := by
      rw [mul_inv_eq_iff_eq_mul]
      exact (hZc z₁ hz₁Z z₀ hz₀Z)
    have hxX : w₁ * x * w₁⁻¹ = x := by
      rw [mul_inv_eq_iff_eq_mul]
      exact hs.X_comm w₁ hw₁X x hs.mem
    have hxz : x * z₀ * x = z₀ := by
      calc x * z₀ * x = z₀ * (x * x) := by rw [← hz₀x]; group
        _ = z₀ := by rw [hx2, mul_one]
    have hg'x : (z₁ * w₁ * z₁) * x * (z₁ * w₁ * z₁)⁻¹ = z₀ := by
      calc (z₁ * w₁ * z₁) * x * (z₁ * w₁ * z₁)⁻¹
          = z₁ * (w₁ * (z₁ * x * z₁⁻¹) * w₁⁻¹) * z₁⁻¹ := by group
        _ = z₁ * ((w₁ * z₀ * w₁⁻¹) * (w₁ * x * w₁⁻¹)) * z₁⁻¹ := by rw [hR1]; group
        _ = z₁ * ((x * z₀) * x) * z₁⁻¹ := by rw [hR2, hxX]
        _ = z₀ := by rw [hxz, hR3]
    have hg'z : (z₁ * w₁ * z₁) * z₀ * (z₁ * w₁ * z₁)⁻¹ = x := by
      calc (z₁ * w₁ * z₁) * z₀ * (z₁ * w₁ * z₁)⁻¹
          = z₁ * (w₁ * (z₁ * z₀ * z₁⁻¹) * w₁⁻¹) * z₁⁻¹ := by group
        _ = z₁ * (x * z₀) * z₁⁻¹ := by rw [hR3, hR2]
        _ = (z₁ * x * z₁⁻¹) * (z₁ * z₀ * z₁⁻¹) := by group
        _ = (z₀ * x) * z₀ := by rw [hR1, hR3]
        _ = (x * z₀) * z₀ := by rw [hz₀x]
        _ = x * (z₀ * z₀) := by group
        _ = x := by rw [hZ2 z₀ hz₀Z, mul_one]
    obtain ⟨q, hq, hqx, hqq⟩ :=
      exists_fixed_sq H hs.memM hx2 ⟨z₁, hz₁Z, hz₁ne⟩ hz₀Z hz₀1 hset hz₁Z rfl
    set g' := z₁ * w₁ * z₁ with hg'
    set y' := g' * q * g'⁻¹ with hy'
    have hy'y' : y' * y' = x := by
      calc y' * y' = g' * (q * q) * g'⁻¹ := by rw [hy']; group
        _ = g' * z₀ * g'⁻¹ := by rw [hqq]
        _ = x := hg'z
    have hqxc : q * x = x * q := by
      calc q * x = (x * q * x⁻¹) * x := by rw [hqx]
        _ = x * q := by group
    have hy'z : y' * z₀ = z₀ * y' := by
      calc y' * z₀ = g' * q * g'⁻¹ * (g' * x * g'⁻¹) := by rw [hg'x]
        _ = g' * (q * x) * g'⁻¹ := by group
        _ = g' * (x * q) * g'⁻¹ := by rw [hqxc]
        _ = (g' * x * g'⁻¹) * (g' * q * g'⁻¹) := by group
        _ = z₀ * y' := by rw [hg'x]
    have hy'M : y' ∈ M := by
      have := Tim77.mem_normalizer_of_commute_of_isTI H.ti hz₀Z hz₀1 hy'z
      rwa [H.normalizer_Z.1] at this
    have hy'N : ∀ y ∈ Z, y' * y * y'⁻¹ ∈ Z := fun y hy =>
      (Subgroup.mem_normalizer_iff.mp (H.Z_normal.2 hy'M) y).mp hy
    exact klein_no_sqrt (Y := Z) (m := x) h4 hZ2 hZc hxN hx2 hz₁Z hz₁ne hy'N hy'y'

end Four

end CFSG.RankThree.GF2n.Smith81
