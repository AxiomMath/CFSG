module

public import CFSG.Quasithin.H13.A6S1372L74n

public section

namespace CFSG.Quasithin.H13.A6

open CFSG.Quasithin

namespace A6L74

variable {Γ : Type*} [Group Γ] [Finite Γ]

omit [Finite Γ] in
theorem conj_eq_of_two_lines {σ a b : Γ} (hσ : σ ^ 3 = 1) (ha3 : a ^ 3 = 1) (ha1 : a ≠ 1)
    (hb3 : b ^ 3 = 1) (hb1 : b ≠ 1) (hab : a ∉ Subgroup.zpowers b)
    (hσa : σ * a * σ⁻¹ ∈ Subgroup.zpowers a ∨ σ * a * σ⁻¹ ∈ Subgroup.zpowers b)
    (hσb : σ * b * σ⁻¹ ∈ Subgroup.zpowers a ∨ σ * b * σ⁻¹ ∈ Subgroup.zpowers b) :
    σ * a * σ⁻¹ = a := by
  rcases hσa with h | h
  · exact conj_eq_of_mem_zpowers hσ ha3 ha1 h
  exfalso
  obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp h
  have hσb1 : σ * b * σ⁻¹ ≠ 1 := by
    intro h1
    apply hb1
    have e : b = σ⁻¹ * (σ * b * σ⁻¹) * σ := by group
    rw [e, h1]
    group
  rcases hσb with h' | h'
  ·
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp h'
    have h2 : σ * (σ * a * σ⁻¹) * σ⁻¹ = a ^ (n * m) := by
      rw [← hm, ← conj_zpow, ← hn, ← zpow_mul]
    have h3 : σ * (σ * (σ * a * σ⁻¹) * σ⁻¹) * σ⁻¹ = (σ * a * σ⁻¹) ^ (n * m) := by
      rw [h2, conj_zpow]
    have e : σ * (σ * (σ * a * σ⁻¹) * σ⁻¹) * σ⁻¹ = (σ * σ * σ) * a * (σ * σ * σ)⁻¹ := by
      simp only [mul_assoc, mul_inv_rev]
    rw [e, ← pow_three', hσ, one_mul, inv_one, mul_one] at h3
    apply hab
    rw [h3]
    exact (Subgroup.zpowers b).zpow_mem h _
  ·
    have hb : b ∈ Subgroup.zpowers (σ * b * σ⁻¹) := mem_zpowers_of_mem_zpowers hb3 h' hσb1
    have h1 : σ * a * σ⁻¹ ∈ Subgroup.zpowers (σ * b * σ⁻¹) := Subgroup.zpowers_le.2 hb h
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp h1
    rw [conj_zpow] at hk
    have hk' : b ^ k = a := by
      have := congrArg (fun w => σ⁻¹ * w * σ) hk
      simpa [mul_assoc] using this
    exact hab (hk' ▸ Subgroup.zpow_mem_zpowers b k)

omit [Finite Γ] in
theorem cube_of_comm_of_equiv {L : Subgroup Γ} (e : ↥L ≃* S1417.SL2) {u t : Γ} (hu : u ∈ L)
    (ht : t ∈ L) (hu3 : u ^ 3 = 1) (hu1 : u ≠ 1) (h : t * u = u * t) : t ^ 3 = 1 := by
  have hx3 : e ⟨u, hu⟩ ^ 3 = 1 := by
    rw [← map_pow]
    have : (⟨u, hu⟩ : ↥L) ^ 3 = 1 := Subtype.ext (by simpa using hu3)
    rw [this, map_one]
  have hx1 : e ⟨u, hu⟩ ≠ 1 := by
    intro h1
    apply hu1
    have : (⟨u, hu⟩ : ↥L) = 1 := e.injective (by rw [h1, map_one])
    simpa using congrArg Subtype.val this
  have hc : e ⟨t, ht⟩ * e ⟨u, hu⟩ = e ⟨u, hu⟩ * e ⟨t, ht⟩ := by
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext h
  have h3 : e ⟨t, ht⟩ ^ 3 = 1 := by
    rcases S1417.SL2_cent_three _ _ hx3 hx1 hc with h' | h' | h'
    · rw [h', one_pow]
    · rw [h', hx3]
    · rw [h', inv_pow, hx3, inv_one]
  have h4 : (⟨t, ht⟩ : ↥L) ^ 3 = 1 := e.injective (by rw [map_pow, h3, map_one])
  simpa using congrArg Subtype.val h4

theorem comm_of_two_blocks {K L₁ L₂ : Subgroup Γ} (e₁ : ↥L₁ ≃* S1417.SL2)
    (e₂ : ↥L₂ ≃* S1417.SL2) (hK3 : ∀ k ∈ K, k ^ 3 = 1)
    (hKc : ∀ a ∈ K, ∀ b ∈ K, a * b = b * a) (hK9 : Nat.card K = 9)
    (hL₁K : ∀ y ∈ L₁, y ^ 3 = 1 → y ∈ K) (hL₂K : ∀ y ∈ L₂, y ^ 3 = 1 → y ∈ K)
    (hc : ∀ a ∈ L₁, ∀ b ∈ L₂, a * b = b * a) (hinf : L₁ ⊓ L₂ = ⊥) {σ : Γ} (hσ : σ ^ 3 = 1)
    (hσK : ∀ k ∈ K, σ * k * σ⁻¹ ∈ K) (hσY : ∀ y ∈ L₁ ⊔ L₂, σ * y * σ⁻¹ ∈ L₁ ⊔ L₂) :
    ∀ k ∈ K, σ * k = k * σ := by
  obtain ⟨d₁, hd₁L, hd₁K, hd₁3, hd₁1, -⟩ := exists_three_of_equiv e₁ hK3 hL₁K
  obtain ⟨d₂, hd₂L, hd₂K, hd₂3, hd₂1, -⟩ := exists_three_of_equiv e₂ hK3 hL₂K
  have hz₁ : Subgroup.zpowers d₁ ≤ L₁ := Subgroup.zpowers_le.2 hd₁L
  have hz₂ : Subgroup.zpowers d₂ ≤ L₂ := Subgroup.zpowers_le.2 hd₂L
  have hmeet : ∀ w, w ∈ L₁ → w ∈ L₂ → w = 1 := fun w h1 h2 => by
    have h : w ∈ L₁ ⊓ L₂ := ⟨h1, h2⟩
    rw [hinf] at h
    exact h
  have hd₂n : d₂ ∉ Subgroup.zpowers d₁ := fun h => hd₂1 (hmeet d₂ (hz₁ h) hd₂L)
  have hd₁n : d₁ ∉ Subgroup.zpowers d₂ := fun h => hd₁1 (hmeet d₁ hd₁L (hz₂ h))
  have hK : Subgroup.zpowers d₁ ⊔ Subgroup.zpowers d₂ = K :=
    sup_zpowers_eq_of_card hK9 hd₁K hd₂K hd₁3 hd₁1 hd₂n
  have hnotP : ∀ u ∈ Subgroup.zpowers d₁, ∀ v ∈ Subgroup.zpowers d₂, u ≠ 1 → v ≠ 1 →
      ∀ t ∈ L₁ ⊔ L₂, t ^ 2 = 1 → t * (u * v) = (u * v) * t → t = 1 := by
    intro u hu v hv hu1 hv1 t ht ht2 htc
    obtain ⟨t₁, ht₁, t₂, ht₂, rfl⟩ := S1417.exists_mul_of_mem_sup_of_commute hc ht
    have huL := hz₁ hu
    have hvL := hz₂ hv
    have hu3 : u ^ 3 = 1 := hK3 u (Subgroup.zpowers_le.2 hd₁K hu)
    have hv3 : v ^ 3 = 1 := hK3 v (Subgroup.zpowers_le.2 hd₂K hv)
    have e1 : t₁ * t₂ * (u * v) = (t₁ * u) * (t₂ * v) := by
      calc t₁ * t₂ * (u * v) = t₁ * (t₂ * u) * v := by group
        _ = t₁ * (u * t₂) * v := by rw [hc u huL t₂ ht₂]
        _ = (t₁ * u) * (t₂ * v) := by group
    have e2 : u * v * (t₁ * t₂) = (u * t₁) * (v * t₂) := by
      calc u * v * (t₁ * t₂) = u * (v * t₁) * t₂ := by group
        _ = u * (t₁ * v) * t₂ := by rw [hc t₁ ht₁ v hvL]
        _ = (u * t₁) * (v * t₂) := by group
    rw [e1, e2] at htc
    obtain ⟨h1, h2⟩ := S1417.eq_of_mul_eq_of_inf_eq_bot hinf (L₁.mul_mem ht₁ huL)
      (L₁.mul_mem huL ht₁) (L₂.mul_mem ht₂ hvL) (L₂.mul_mem hvL ht₂) htc
    have ht₁3 := cube_of_comm_of_equiv e₁ huL ht₁ hu3 hu1 h1
    have ht₂3 := cube_of_comm_of_equiv e₂ hvL ht₂ hv3 hv1 h2
    have hcomm12 : t₁ * t₂ = t₂ * t₁ := hc t₁ ht₁ t₂ ht₂
    have hsq : t₁ ^ 2 * t₂ ^ 2 = 1 := by
      rw [← ht2, sq, sq, sq]
      calc t₁ * t₁ * (t₂ * t₂) = t₁ * (t₁ * t₂) * t₂ := by group
        _ = t₁ * (t₂ * t₁) * t₂ := by rw [hcomm12]
        _ = t₁ * t₂ * (t₁ * t₂) := by group
    have h1sq : t₁ ^ 2 = 1 := by
      refine hmeet _ (L₁.pow_mem ht₁ 2) ?_
      rw [eq_inv_of_mul_eq_one_left hsq]
      exact L₂.inv_mem (L₂.pow_mem ht₂ 2)
    have h2sq : t₂ ^ 2 = 1 := by
      rw [h1sq, one_mul] at hsq
      exact hsq
    have ht₁1 : t₁ = 1 := by
      calc t₁ = t₁ ^ 3 * (t₁ ^ 2)⁻¹ := by group
        _ = 1 := by rw [ht₁3, h1sq, inv_one, one_mul]
    have ht₂1 : t₂ = 1 := by
      calc t₂ = t₂ ^ 3 * (t₂ ^ 2)⁻¹ := by group
        _ = 1 := by rw [ht₂3, h2sq, inv_one, one_mul]
    rw [ht₁1, ht₂1, one_mul]
  have hsplit : ∀ z ∈ K, (∃ t ∈ L₁ ⊔ L₂, t ^ 2 = 1 ∧ t ≠ 1 ∧ t * z = z * t) →
      z ∈ Subgroup.zpowers d₁ ∨ z ∈ Subgroup.zpowers d₂ := by
    rintro z hz ⟨t, ht, ht2, ht1, htz⟩
    rw [← hK] at hz
    obtain ⟨u, hu, v, hv, rfl⟩ := S1417.exists_mul_of_mem_sup_of_commute
      (fun a ha b hb => hKc a (Subgroup.zpowers_le.2 hd₁K ha) b (Subgroup.zpowers_le.2 hd₂K hb))
      hz
    by_cases hu1 : u = 1
    · right
      rw [hu1, one_mul]
      exact hv
    by_cases hv1 : v = 1
    · left
      rw [hv1, mul_one]
      exact hu
    exact absurd (hnotP u hu v hv hu1 hv1 t ht ht2 htz) ht1
  have hPσ : ∀ w, (∃ t ∈ L₁ ⊔ L₂, t ^ 2 = 1 ∧ t ≠ 1 ∧ t * w = w * t) →
      ∃ t ∈ L₁ ⊔ L₂, t ^ 2 = 1 ∧ t ≠ 1 ∧ t * (σ * w * σ⁻¹) = (σ * w * σ⁻¹) * t := by
    rintro w ⟨t, ht, ht2, ht1, htw⟩
    refine ⟨σ * t * σ⁻¹, hσY t ht, by rw [conj_pow, ht2, mul_one, mul_inv_cancel], ?_, ?_⟩
    · intro h
      apply ht1
      calc t = σ⁻¹ * (σ * t * σ⁻¹) * σ := by group
        _ = 1 := by rw [h]; group
    · calc σ * t * σ⁻¹ * (σ * w * σ⁻¹) = σ * (t * w) * σ⁻¹ := by group
        _ = σ * (w * t) * σ⁻¹ := by rw [htw]
        _ = σ * w * σ⁻¹ * (σ * t * σ⁻¹) := by group
  obtain ⟨t₀, ht₀2, ht₀1⟩ := SL2_exists_two
  have hinv : ∀ {L : Subgroup Γ} (f : ↥L ≃* S1417.SL2), ∃ t ∈ L, t ^ 2 = 1 ∧ t ≠ 1 := by
    intro L f
    refine ⟨(f.symm t₀ : Γ), (f.symm t₀).2, ?_, ?_⟩
    · have h : (f.symm t₀) ^ 2 = 1 := by rw [← map_pow, ht₀2, map_one]
      simpa using congrArg Subtype.val h
    · intro h
      apply ht₀1
      have h' : f.symm t₀ = 1 := Subtype.ext h
      simpa using congrArg f h'
  obtain ⟨s₂, hs₂L, hs₂2, hs₂1⟩ := hinv e₂
  obtain ⟨s₁, hs₁L, hs₁2, hs₁1⟩ := hinv e₁
  have hP₁ : ∃ t ∈ L₁ ⊔ L₂, t ^ 2 = 1 ∧ t ≠ 1 ∧ t * d₁ = d₁ * t :=
    ⟨s₂, Subgroup.mem_sup_right hs₂L, hs₂2, hs₂1, (hc d₁ hd₁L s₂ hs₂L).symm⟩
  have hP₂ : ∃ t ∈ L₁ ⊔ L₂, t ^ 2 = 1 ∧ t ≠ 1 ∧ t * d₂ = d₂ * t :=
    ⟨s₁, Subgroup.mem_sup_left hs₁L, hs₁2, hs₁1, hc s₁ hs₁L d₂ hd₂L⟩
  have hσ₁ := hsplit _ (hσK d₁ hd₁K) (hPσ d₁ hP₁)
  have hσ₂ := hsplit _ (hσK d₂ hd₂K) (hPσ d₂ hP₂)
  have hfix₁ : σ * d₁ * σ⁻¹ = d₁ :=
    conj_eq_of_two_lines hσ hd₁3 hd₁1 hd₂3 hd₂1 hd₁n hσ₁ hσ₂
  have hfix₂ : σ * d₂ * σ⁻¹ = d₂ :=
    conj_eq_of_two_lines hσ hd₂3 hd₂1 hd₁3 hd₁1 hd₂n hσ₂.symm hσ₁.symm
  have hle : K ≤ Subgroup.centralizer ({σ} : Set Γ) := by
    rw [← hK]
    refine sup_le (Subgroup.zpowers_le.2 ?_) (Subgroup.zpowers_le.2 ?_)
    · rw [Subgroup.mem_centralizer_singleton_iff]
      exact (mul_inv_eq_iff_eq_mul.mp hfix₁).symm
    · rw [Subgroup.mem_centralizer_singleton_iff]
      exact (mul_inv_eq_iff_eq_mul.mp hfix₂).symm
  intro k hk
  exact (Subgroup.mem_centralizer_singleton_iff.mp (hle hk)).symm

theorem comm_of_blocks {K Y : Subgroup Γ} {I : Finset (Subgroup Γ)} (hK3 : ∀ k ∈ K, k ^ 3 = 1)
    (hKc : ∀ a ∈ K, ∀ b ∈ K, a * b = b * a) (hK9 : Nat.card K = 9)
    (hYK : ∀ y ∈ Y, y ^ 3 = 1 → y ∈ K) (hKY : ∀ k ∈ K, ∀ y ∈ Y, k * y * k⁻¹ ∈ Y)
    (hY : Y = ⨆ L ∈ I, L)
    (hcomm : ∀ L ∈ I, ∀ L' ∈ I, L ≠ L' → ∀ a ∈ L, ∀ b ∈ L', a * b = b * a)
    (hindep : ∀ L ∈ I, L ⊓ ⨆ L' ∈ I, ⨆ (_ : L' ≠ L), L' = ⊥)
    (hnat : ∀ L ∈ I, Nonempty (↥L ≃* S1417.SL2)) (hI : I.Nonempty) {σ : Γ} (hσ : σ ^ 3 = 1)
    (hσK : ∀ k ∈ K, σ * k * σ⁻¹ ∈ K) (hσY : ∀ y ∈ Y, σ * y * σ⁻¹ ∈ Y) :
    ∀ k ∈ K, σ * k = k * σ := by
  classical
  have hLY : ∀ L ∈ I, L ≤ Y := fun L hL => hY ▸ le_iSup₂_of_le L hL le_rfl
  have hLK : ∀ L ∈ I, ∀ y ∈ L, y ^ 3 = 1 → y ∈ K := fun L hL y hy => hYK y (hLY L hL hy)
  have hinf : ∀ L ∈ I, ∀ L' ∈ I, L ≠ L' → L ⊓ L' = ⊥ := fun L hL L' hL' hne => by
    rw [eq_bot_iff, ← hindep L hL]
    exact inf_le_inf_left _ (le_iSup₂_of_le L' hL' (le_iSup_of_le (Ne.symm hne) le_rfl))
  rcases Nat.lt_or_ge 2 I.card with h3 | h2
  ·
    exfalso
    obtain ⟨L₁, L₂, L₃, h1, h2', h3', h12, h13, h23⟩ := Finset.two_lt_card_iff.mp h3
    obtain ⟨e₁⟩ := hnat L₁ h1
    obtain ⟨e₂⟩ := hnat L₂ h2'
    obtain ⟨e₃⟩ := hnat L₃ h3'
    obtain ⟨d₁, hd₁L, hd₁K, hd₁3, hd₁1, -⟩ := exists_three_of_equiv e₁ hK3 (hLK L₁ h1)
    obtain ⟨d₂, hd₂L, hd₂K, -, hd₂1, -⟩ := exists_three_of_equiv e₂ hK3 (hLK L₂ h2')
    obtain ⟨d₃, hd₃L, hd₃K, -, hd₃1, -⟩ := exists_three_of_equiv e₃ hK3 (hLK L₃ h3')
    have hd₂n : d₂ ∉ Subgroup.zpowers d₁ := by
      intro h
      apply hd₂1
      have hm : d₂ ∈ L₁ ⊓ L₂ := ⟨Subgroup.zpowers_le.2 hd₁L h, hd₂L⟩
      rw [hinf L₁ h1 L₂ h2' h12] at hm
      exact hm
    have hK := sup_zpowers_eq_of_card hK9 hd₁K hd₂K hd₁3 hd₁1 hd₂n
    have hd₃' : d₃ ∈ L₁ ⊔ L₂ := by
      rw [← hK] at hd₃K
      exact sup_le_sup (Subgroup.zpowers_le.2 hd₁L) (Subgroup.zpowers_le.2 hd₂L) hd₃K
    have hle₁ : L₁ ≤ ⨆ L' ∈ I, ⨆ (_ : L' ≠ L₃), L' :=
      le_iSup₂_of_le (f := fun L' (_ : L' ∈ I) => ⨆ (_ : L' ≠ L₃), L') L₁ h1
        (le_iSup_of_le h13 le_rfl)
    have hle₂ : L₂ ≤ ⨆ L' ∈ I, ⨆ (_ : L' ≠ L₃), L' :=
      le_iSup₂_of_le (f := fun L' (_ : L' ∈ I) => ⨆ (_ : L' ≠ L₃), L') L₂ h2'
        (le_iSup_of_le h23 le_rfl)
    have hm : d₃ ∈ L₃ ⊓ ⨆ L' ∈ I, ⨆ (_ : L' ≠ L₃), L' := ⟨hd₃L, sup_le hle₁ hle₂ hd₃'⟩
    rw [hindep L₃ h3'] at hm
    exact hd₃1 hm
  rcases Nat.lt_or_ge I.card 2 with h1 | h2'
  ·
    have hc1 : I.card = 1 := by
      have := hI.card_pos
      omega
    obtain ⟨L, rfl⟩ := Finset.card_eq_one.mp hc1
    have hYL : Y = L := by
      rw [hY]
      simp
    subst hYL
    obtain ⟨e⟩ := hnat Y (Finset.mem_singleton_self Y)
    exact comm_of_one_block e hK3 hKc hK9 hYK hKY hσ hσK hσY
  ·
    have hc2 : I.card = 2 := by omega
    obtain ⟨L₁, L₂, hne, rfl⟩ := Finset.card_eq_two.mp hc2
    have hm₁ : L₁ ∈ ({L₁, L₂} : Finset (Subgroup Γ)) := by simp
    have hm₂ : L₂ ∈ ({L₁, L₂} : Finset (Subgroup Γ)) := by simp
    have hYL : Y = L₁ ⊔ L₂ := by
      rw [hY]
      apply le_antisymm
      · refine iSup₂_le fun L hL => ?_
        rw [Finset.mem_insert, Finset.mem_singleton] at hL
        rcases hL with rfl | rfl
        · exact le_sup_left
        · exact le_sup_right
      · exact sup_le (le_iSup₂_of_le L₁ hm₁ le_rfl) (le_iSup₂_of_le L₂ hm₂ le_rfl)
    subst hYL
    obtain ⟨e₁⟩ := hnat L₁ hm₁
    obtain ⟨e₂⟩ := hnat L₂ hm₂
    exact comm_of_two_blocks e₁ e₂ hK3 hKc hK9 (hLK L₁ hm₁) (hLK L₂ hm₂)
      (hcomm L₁ hm₁ L₂ hm₂ hne) (hinf L₁ hm₁ L₂ hm₂ hne) hσ hσK hσY

end A6L74

end CFSG.Quasithin.H13.A6
