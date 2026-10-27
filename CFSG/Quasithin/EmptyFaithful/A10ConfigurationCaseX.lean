module

public import CFSG.Quasithin.EmptyFaithful.A10ConfigurationCaseK
public import CFSG.Quasithin.Background.A1cTransferVariants
public import CFSG.Quasithin.Background.A4Bridge

public section

namespace CFSG.Quasithin.A10

open CFSG.Open CFSG.Quasithin S4

variable {G : Type*} [Group G]

theorem exists_conj_mem_of_sq [Finite G] {S H : Subgroup G}
    (hS : CFSG.QuasithinUnique.IsSylowTwoOf S H) {u : G} (huH : u ∈ H) (hu : u * u = 1) :
    ∃ h ∈ H, h⁻¹ * u * h ∈ S := by
  obtain ⟨S', hS', hPS'⟩ := A4.exists_isSylowTwoOf_ge (P := Subgroup.zpowers u) (H := H)
    (Subgroup.zpowers_le.2 huH) (isPGroup_zpowers_of_mul_self hu)
  obtain ⟨h, hh, hconj⟩ := A4.exists_conj_of_isSylowTwoOf hS hS'
  exact ⟨h, hh, (hconj u).1 (hPS' (Subgroup.mem_zpowers u))⟩

namespace Emb

variable {T M : Subgroup G} (E : Emb G T M)

theorem zG_of_D145 [Finite G] (hzK : ∀ y : G, y ∈ E.zK ↔ ∃ w ∈ Zset true true, E.ι w = y)
    {w : Wc} (hw : D1 w = true ∨ D4 w = true ∨ D5 w = true) :
    ∃ g : G, g⁻¹ * E.z * g = E.ι w := by
  have key : ∀ v : Wc, v⁻¹ * w * v ∈ A2 → (D1 (v⁻¹ * w * v) = true ∨ D4 (v⁻¹ * w * v) = true ∨
      D5 (v⁻¹ * w * v) = true) → ∃ g : G, g⁻¹ * E.z * g = E.ι w := by
    intro v hv hcls
    obtain ⟨k, hk, hkz⟩ := (hzK _).2 ⟨v⁻¹ * w * v, mem_Zset_true _ hv hcls, rfl⟩
    refine ⟨k * (E.ι v)⁻¹, ?_⟩
    have : E.ι (v⁻¹ * w * v) = (E.ι v)⁻¹ * E.ι w * E.ι v := by simp
    calc (k * (E.ι v)⁻¹)⁻¹ * E.z * (k * (E.ι v)⁻¹) = E.ι v * (k⁻¹ * E.z * k) * (E.ι v)⁻¹ := by
          group
      _ = E.ι v * ((E.ι v)⁻¹ * E.ι w * E.ι v) * (E.ι v)⁻¹ := by rw [hkz, ← this]
      _ = E.ι w := by group
  rcases hw with h | h | h
  · obtain ⟨v, hv⟩ := (cls_z0 w).2 h
    refine ⟨E.ι v, ?_⟩
    rw [← hv]
    simp [z]
  · obtain ⟨v, hv⟩ := D4_into_B w h
    exact key v hv (Or.inr (Or.inl (D4_conj h v)))
  · obtain ⟨v, hv⟩ := D5_into_B w h
    exact key v hv (Or.inr (Or.inr (D5_conj h v)))

theorem ι_mem_J {w : Wc} (hw : w ∈ Jh) : E.ι w ∈ E.J := Subgroup.mem_map_of_mem _ hw

theorem conj_ι_comm_t {y : G} (hy : y ∈ E.Y) : y⁻¹ * E.t * y = E.t := by
  have := E.mem_Y.1 hy
  calc y⁻¹ * E.t * y = y⁻¹ * (E.t * y) := by group
    _ = y⁻¹ * (y * E.t) := by rw [this]
    _ = E.t := by group

theorem SC1_G [Finite G] (hT : quasithinIsSylowTwo T) (hGz : Subgroup.centralizer ({E.z} : Set G) = T)
    (hzK : ∀ y : G, y ∈ E.zK ↔ ∃ w ∈ Zset true true, E.ι w = y) {w : Wc} (hw : w ∈ T1h)
    (hw2 : w * w = 1) (hw1 : w ≠ 1) (hwt : w ≠ t0) {y : G} (hy : y ∈ E.Y)
    (hyJ : y⁻¹ * E.ι w * y ∈ E.J) : ∃ w' ∈ T1h, E.ι w' = y⁻¹ * E.ι w * y := by
  obtain ⟨w₁, hw₁J, hw₁⟩ := Subgroup.mem_map.mp hyJ
  have hw₁1 : w₁ ≠ 1 := by
    rintro rfl
    rw [map_one] at hw₁
    apply hw1
    apply E.injective
    rw [map_one]
    calc E.ι w = y * (y⁻¹ * E.ι w * y) * y⁻¹ := by group
      _ = 1 := by rw [← hw₁]; group
  have hw₁2 : w₁ * w₁ = 1 := by
    apply E.injective
    rw [map_mul, hw₁, map_one]
    calc y⁻¹ * E.ι w * y * (y⁻¹ * E.ι w * y) = y⁻¹ * (E.ι w * E.ι w) * y := by group
      _ = 1 := by rw [← map_mul, hw2, map_one]; group
  have hD23w : D2 w = true ∨ D3 w = true := T1h_involution w hw hw2 hw1
  have hnzw : ¬ ∃ g : G, g⁻¹ * E.z * g = E.ι w := by
    rcases hD23w with h | h
    · exact E.not_mem_zG_of_D236 hGz hT (Or.inl h)
    · exact E.not_mem_zG_of_D236 hGz hT (Or.inr (Or.inl h))
  have hconj : ∀ x x' : Wc, E.ι x = y⁻¹ * E.ι x' * y → (¬ ∃ g : G, g⁻¹ * E.z * g = E.ι x') →
      ¬ (D1 x = true ∨ D4 x = true ∨ D5 x = true) := by
    intro x x' hx hn h
    obtain ⟨g, hg⟩ := E.zG_of_D145 hzK h
    apply hn
    refine ⟨g * y⁻¹, ?_⟩
    calc (g * y⁻¹)⁻¹ * E.z * (g * y⁻¹) = y * (g⁻¹ * E.z * g) * y⁻¹ := by group
      _ = y * (y⁻¹ * E.ι x' * y) * y⁻¹ := by rw [hg, hx]
      _ = E.ι x' := by group
  have hD23w₁ : D2 w₁ = true ∨ D3 w₁ = true := by
    have hn := hconj w₁ w hw₁ hnzw
    rcases involution_partition w₁ hw₁2 hw₁1 with h | h | h | h | h | h
    · exact absurd (Or.inl h) hn
    · exact Or.inl h
    · exact Or.inr h
    · exact absurd (Or.inr (Or.inl h)) hn
    · exact absurd (Or.inr (Or.inr h)) hn
    · exact absurd hw₁J (D6_not_mem_Jh h)
  have hwJ : w ∈ Jh := T1h_le_Jh hw
  have htJ : t0 ∈ Jh := T1h_le_Jh t0_mem_T1h
  have hsq_mul : ∀ x ∈ Jh, x * x = 1 → (t0 * x) * (t0 * x) = 1 := by
    intro x hx hx2
    calc t0 * x * (t0 * x) = t0 * (x * t0) * x := by group
      _ = t0 * (t0 * x) * x := by rw [t0_central_Jh x hx]
      _ = (t0 * t0) * (x * x) := by group
      _ = 1 := by rw [t0_sq, hx2, mul_one]
  have htw : t0 * w ∈ T1h := T1h.mul_mem t0_mem_T1h hw
  have htw2 : (t0 * w) * (t0 * w) = 1 := hsq_mul w hwJ hw2
  have hne_of_mul : ∀ x : Wc, x ≠ t0 → t0 * x ≠ 1 := by
    intro x hx h
    apply hx
    have h2 : x = t0⁻¹ := eq_inv_of_mul_eq_one_right h
    rw [h2]
    exact inv_eq_of_mul_eq_one_right t0_sq
  have htw1 : t0 * w ≠ 1 := hne_of_mul w hwt
  have hD23tw : D2 (t0 * w) = true ∨ D3 (t0 * w) = true := T1h_involution (t0 * w) htw htw2 htw1
  have hnztw : ¬ ∃ g : G, g⁻¹ * E.z * g = E.ι (t0 * w) := by
    rcases hD23tw with h | h
    · exact E.not_mem_zG_of_D236 hGz hT (Or.inl h)
    · exact E.not_mem_zG_of_D236 hGz hT (Or.inr (Or.inl h))
  have hιtw : E.ι (t0 * w₁) = y⁻¹ * E.ι (t0 * w) * y := by
    have ht : E.ι t0 = y⁻¹ * E.ι t0 * y := (E.conj_ι_comm_t hy).symm
    rw [map_mul, map_mul, hw₁]
    calc E.ι t0 * (y⁻¹ * E.ι w * y) = (y⁻¹ * E.ι t0 * y) * (y⁻¹ * E.ι w * y) := by rw [← ht]
      _ = y⁻¹ * (E.ι t0 * E.ι w) * y := by group
  have hD' : D2 (t0 * w₁) = true ∨ D3 (t0 * w₁) = true ∨ t0 * w₁ = 1 := by
    by_cases h1 : t0 * w₁ = 1
    · exact Or.inr (Or.inr h1)
    have hn := hconj (t0 * w₁) (t0 * w) hιtw hnztw
    rcases involution_partition (t0 * w₁) (hsq_mul w₁ hw₁J hw₁2) h1 with h | h | h | h | h | h
    · exact absurd (Or.inl h) hn
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact absurd (Or.inr (Or.inl h)) hn
    · exact absurd (Or.inr (Or.inr h)) hn
    · exact absurd (Jh.mul_mem htJ hw₁J) (D6_not_mem_Jh h)
  exact ⟨w₁, SC1_fact w₁ hw₁J hw₁1 hw₁2 hD23w₁ hD', hw₁⟩

theorem not_mem_X_of_transfer [Finite G] (hT : quasithinIsSylowTwo T)
    (hM : quasithinIsMaxTwoLocal M) {Kw : Subgroup Wc} (hKJ : Kw ≤ Jh)
    (hKn : ∀ h ∈ Jh, ∀ k ∈ Kw, h * k * h⁻¹ ∈ Kw) (hab : ⁅Jh, Jh⁆ ≤ Kw) {g : G}
    (hg : g ∈ E.J) (hgK : g ∉ Kw.map E.ι)
    (h : ∀ (m : ℤ) (a : G), a ∈ E.Y → a⁻¹ * g ^ m * a ∈ E.J →
      (g ^ m)⁻¹ * (a⁻¹ * g ^ m * a) ∈ Kw.map E.ι) : g ∉ E.X := by
  have hsyl := E.isSylowTwoOf_J hT hM
  refine not_mem_oTwoUpper_of_transfer (X := E.Y) (H := E.J) (K := Kw.map E.ι)
    E.J_le_centralizer_t E.J_isPGroup hsyl.2.2 (Subgroup.map_mono hKJ) ?_ ?_ hg hgK h
  · rintro _ ⟨h', hh', rfl⟩ _ ⟨k', hk', rfl⟩
    refine ⟨h' * k' * h'⁻¹, hKn h' hh' k' hk', ?_⟩
    simp
  · have h1 : ⁅E.J, E.J⁆ = (⁅Jh, Jh⁆).map E.ι := (Subgroup.map_commutator Jh Jh E.ι).symm
    rw [h1]
    exact Subgroup.map_mono hab

theorem sq_ι {w : Wc} (hw2 : w * w = 1) : E.ι w ^ 2 = 1 := by
  rw [pow_two, ← map_mul, hw2, map_one]

theorem noncentral_not_mem_X [Finite G] (hT : quasithinIsSylowTwo T) (hM : quasithinIsMaxTwoLocal M)
    (hGz : Subgroup.centralizer ({E.z} : Set G) = T)
    (hzK : ∀ y : G, y ∈ E.zK ↔ ∃ w ∈ Zset true true, E.ι w = y) {w : Wc} (hw : w ∈ T1h)
    (hw2 : w * w = 1) (hw1 : w ≠ 1) (hwt : w ≠ t0) : E.ι w ∉ E.X := by
  have hg2 : E.ι w ^ 2 = 1 := E.sq_ι hw2
  refine E.not_mem_X_of_transfer hT hM Kr_le_Jh Kr_conj commutator_Jh_le_Kr
    (E.ι_mem_J (T1h_le_Jh hw)) ?_ ?_
  · intro hmem
    exact r_one_not_mem_Kr w hw hw2 hw1 hwt ((Subgroup.mem_map_iff_mem E.injective).1 hmem)
  · intro m a ha haJ
    rcases Int.even_or_odd' m with ⟨j, rfl | rfl⟩
    · have h1 : E.ι w ^ (2 * j) = 1 := by rw [zpow_mul]; simp [hg2]
      rw [h1]
      simp
    · have h1 : E.ι w ^ (2 * j + 1) = E.ι w := by rw [zpow_add, zpow_mul]; simp [hg2]
      rw [h1] at haJ ⊢
      obtain ⟨w', hw', hw'eq⟩ := E.SC1_G hT hGz hzK hw hw2 hw1 hwt ha haJ
      have hw'2 : w' * w' = 1 := by
        apply E.injective
        rw [map_mul, hw'eq, map_one]
        calc a⁻¹ * E.ι w * a * (a⁻¹ * E.ι w * a) = a⁻¹ * (E.ι w * E.ι w) * a := by group
          _ = 1 := by rw [← map_mul, hw2, map_one]; group
      have hw'1 : w' ≠ 1 := by
        rintro rfl
        rw [map_one] at hw'eq
        apply hw1
        apply E.injective
        rw [map_one]
        calc E.ι w = a * (a⁻¹ * E.ι w * a) * a⁻¹ := by group
          _ = 1 := by rw [← hw'eq]; group
      have hw't : w' ≠ t0 := by
        intro h
        apply hwt
        apply E.injective
        have h5 : a⁻¹ * E.ι t0 * a = E.ι t0 := E.conj_ι_comm_t ha
        have h6 : E.ι t0 * a = a * E.ι t0 := by
          calc E.ι t0 * a = a * (a⁻¹ * E.ι t0 * a) := by group
            _ = a * E.ι t0 := by rw [h5]
        calc E.ι w = a * (a⁻¹ * E.ι w * a) * a⁻¹ := by group
          _ = a * E.ι w' * a⁻¹ := by rw [hw'eq]
          _ = a * E.ι t0 * a⁻¹ := by rw [h]
          _ = E.ι t0 * a * a⁻¹ := by rw [h6]
          _ = E.ι t0 := by group
      have hmem := SC3_fact w hw w' hw' hw2 hw'2 hw1 hwt hw'1 hw't
      rw [← hw'eq, ← map_inv, ← map_mul]
      exact Subgroup.mem_map_of_mem _ hmem

theorem r_not_mem_X [Finite G] (hT : quasithinIsSylowTwo T) (hM : quasithinIsMaxTwoLocal M) :
    E.ι ⟨r, 1, false⟩ ∉ E.X := by
  set ρ : G := E.ι ⟨r, 1, false⟩ with hρ
  have hρ2 : ρ * ρ = E.t := by rw [hρ, ← map_mul, r_one_sq]; rfl
  have hρ4 : ρ ^ (4 : ℤ) = 1 := by
    have h4 : ρ * ρ * (ρ * ρ) = 1 := by
      rw [hρ2]
      exact E.t_sq
    calc ρ ^ (4 : ℤ) = ρ * ρ * (ρ * ρ) := by
          rw [show (4 : ℤ) = ((4 : ℕ) : ℤ) by norm_num, zpow_natCast]
          simp only [pow_succ, pow_zero, one_mul, mul_assoc]
      _ = 1 := h4
  have hρ3 : ρ ^ (3 : ℤ) = E.ι ⟨r3, 1, false⟩ := by
    rw [hρ, zpow_ofNat, ← map_pow, r_one_pow3]
  have hsq3 : E.ι ⟨r3, 1, false⟩ * E.ι ⟨r3, 1, false⟩ = E.t := by
    rw [← map_mul, r3_one_sq]; rfl
  refine E.not_mem_X_of_transfer hT hM Kt_le_Jh Kt_conj commutator_Jh_le_Kt
    (E.ι_mem_J (T1h_le_Jh r_one_mem)) ?_ ?_
  · intro hmem
    exact r_one_not_mem_Kt ((Subgroup.mem_map_iff_mem E.injective).1 hmem)
  · intro m a ha haJ
    have hat : a⁻¹ * E.t * a = E.t := E.conj_ι_comm_t ha
    have hsqconj : ∀ x : G, x * x = E.t → (a⁻¹ * x * a) * (a⁻¹ * x * a) = E.t := by
      intro x hx
      calc a⁻¹ * x * a * (a⁻¹ * x * a) = a⁻¹ * (x * x) * a := by group
        _ = E.t := by rw [hx, hat]
    rw [zpow_eq_zpow_emod m hρ4] at haJ ⊢
    have hm : m % 4 = 0 ∨ m % 4 = 1 ∨ m % 4 = 2 ∨ m % 4 = 3 := by omega
    rcases hm with h | h | h | h <;> rw [h] at haJ ⊢
    · simp
    · rw [zpow_one] at haJ ⊢
      obtain ⟨w₁, hw₁J, hw₁⟩ := Subgroup.mem_map.mp haJ
      have hw₁2 : w₁ * w₁ = t0 := E.injective (by rw [map_mul, hw₁]; exact hsqconj ρ hρ2)
      have hmem := (SC2_fact w₁ hw₁J hw₁2).1
      rw [← hw₁, hρ, ← map_inv, ← map_mul]
      exact Subgroup.mem_map_of_mem _ hmem
    · have : ρ ^ (2 : ℤ) = E.t := by rw [zpow_two]; exact hρ2
      rw [this, hat]
      simp
    · rw [hρ3] at haJ ⊢
      obtain ⟨w₁, hw₁J, hw₁⟩ := Subgroup.mem_map.mp haJ
      have hw₁2 : w₁ * w₁ = t0 := E.injective (by rw [map_mul, hw₁]; exact hsqconj _ hsq3)
      have hmem := (SC2_fact w₁ hw₁J hw₁2).2
      rw [← hw₁, ← map_inv, ← map_mul]
      exact Subgroup.mem_map_of_mem _ hmem

structure CaseB (E : Emb G T M) : Prop where
  sylow : quasithinIsSylowTwo T
  maxLocal : quasithinIsMaxTwoLocal M
  gz : Subgroup.centralizer ({E.z} : Set G) = T
  zK : ∀ y : G, y ∈ E.zK ↔ ∃ w ∈ Zset true true, E.ι w = y

theorem T1_inf_X [Finite G] (hB : E.CaseB) {y : G} (hy : y ∈ E.T₁) (hyX : y ∈ E.X) :
    y = 1 ∨ y = E.t := by
  obtain ⟨w, hw, rfl⟩ := hy
  rcases T1h_cases w hw with rfl | rfl | rfl | rfl | ⟨h2, h1, ht⟩
  · left; exact map_one _
  · right; rfl
  · exact absurd hyX (E.r_not_mem_X hB.sylow hB.maxLocal)
  · exfalso
    apply E.r_not_mem_X hB.sylow hB.maxLocal
    have h := E.X.inv_mem hyX
    rwa [← map_inv, r3_one_inv] at h
  · exact absurd hyX (E.noncentral_not_mem_X hB.sylow hB.maxLocal hB.gz hB.zK hw h2 h1 ht)

theorem T₂_le_J : E.T₂ ≤ E.J := Subgroup.map_mono T2h_le_Jh

theorem t_not_mem_T₂ : E.t ∉ E.T₂ := by
  intro h
  exact t0_not_mem_T2h ((Subgroup.mem_map_iff_mem E.injective).1 h)

theorem card_T₂ : Nat.card E.T₂ = 8 := by
  unfold T₂
  rw [card_map_of_inj E.injective, card_T2h]

theorem card_Kt_G : Nat.card (Kt.map E.ι) = 16 := by
  rw [card_map_of_inj E.injective, card_Kt]

theorem orderOf_t : orderOf E.t = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact orderOf_eq_prime (by rw [pow_two]; exact E.t_sq) E.t_ne_one

theorem J_inf_X [Finite G] (hB : E.CaseB) (hT₂ : E.T₂ ≤ E.X) (htX : E.t ∉ E.X) {y : G}
    (hyJ : y ∈ E.J) (hyX : y ∈ E.X) : y ∈ E.T₂ := by
  obtain ⟨w, hw, rfl⟩ := hyJ
  obtain ⟨a, ha, b, hb, rfl⟩ := Jh_eq_mul w hw
  have hbT : E.ι b ∈ E.T₂ := Subgroup.mem_map_of_mem _ hb
  have haX : E.ι a ∈ E.X := by
    have h := E.X.mul_mem hyX (E.X.inv_mem (hT₂ hbT))
    rwa [map_mul, mul_inv_cancel_right] at h
  rcases E.T1_inf_X hB (Subgroup.mem_map_of_mem _ ha) haX with h | h
  · have : a = 1 := E.injective (by rw [h, map_one])
    rw [this, one_mul]
    exact hbT
  · exact absurd (h ▸ haX) htX

theorem t_not_mem_X [Finite G] (hB : E.CaseB) (hT₂ : E.T₂ ≤ E.X) : E.t ∉ E.X := by
  intro htX
  have hsyl := E.isSylowTwoOf_J hB.sylow hB.maxLocal
  have hsylX : CFSG.QuasithinUnique.IsSylowTwoOf (E.J ⊓ E.X) E.X :=
    A4.isSylowTwoOf_inf_normal hsyl E.X_le_Y (le_normalizer_oTwoUpper E.Y)
  have hPeq : E.J ⊓ E.X = Kt.map E.ι := by
    ext y
    constructor
    · rintro ⟨hyJ, hyX⟩
      obtain ⟨w, hw, rfl⟩ := hyJ
      obtain ⟨a, ha, b, hb, rfl⟩ := Jh_eq_mul w hw
      have hbT : E.ι b ∈ E.T₂ := Subgroup.mem_map_of_mem _ hb
      have haX : E.ι a ∈ E.X := by
        have h := E.X.mul_mem hyX (E.X.inv_mem (hT₂ hbT))
        rwa [map_mul, mul_inv_cancel_right] at h
      refine ⟨a * b, mul_mem_Kt a ha b hb ?_, rfl⟩
      rcases E.T1_inf_X hB (Subgroup.mem_map_of_mem _ ha) haX with h | h
      · exact Or.inl (E.injective (by rw [h, map_one]))
      · exact Or.inr (E.injective h)
    · rintro ⟨w, hw, rfl⟩
      obtain ⟨b, hb, hwb⟩ := Kt_cases w hw
      have hbT : E.ι b ∈ E.T₂ := Subgroup.mem_map_of_mem _ hb
      rcases hwb with rfl | rfl
      · exact ⟨E.T₂_le_J hbT, hT₂ hbT⟩
      · rw [map_mul]
        exact ⟨E.J.mul_mem (E.ι_mem_J (T1h_le_Jh t0_mem_T1h)) (E.T₂_le_J hbT),
          E.X.mul_mem htX (hT₂ hbT)⟩
  have hQP : E.T₂ ≤ E.J ⊓ E.X := fun y hy => ⟨E.T₂_le_J hy, hT₂ hy⟩
  have hQidx : E.T₂.relIndex (E.J ⊓ E.X) = 2 := by
    have h := Subgroup.relIndex_mul_card E.T₂ (E.J ⊓ E.X)
    have hc : Nat.card ↥(E.J ⊓ E.X) = 16 := by rw [hPeq]; exact E.card_Kt_G
    rw [inf_eq_left.mpr hQP, E.card_T₂, hc] at h
    omega
  have hu : ∀ x ∈ E.X, x⁻¹ * E.t * x ∉ E.T₂ := by
    intro x hx
    rw [E.conj_ι_comm_t (E.X_le_Y hx)]
    exact E.t_not_mem_T₂
  have h := thompson_transfer_lemma_subgroup (X := E.X) (P := E.J ⊓ E.X) (Q := E.T₂)
    inf_le_right hsylX.2.1 hsylX.2.2 hQP hQidx htX E.orderOf_t hu
  apply h
  rw [← oTwoUpper_eq_pResidualOf, X, oTwoUpper_oTwoUpper]
  exact htX

theorem tK_cases [Finite G] (hB : E.CaseB)
    (hcon : ∀ k ∈ E.K, ∀ w ∈ A2, D3 w = true → k⁻¹ * E.t * k ≠ E.ι w) {k : G} (hk : k ∈ E.K) :
    k⁻¹ * E.t * k = E.t ∨ k⁻¹ * E.t * k = E.ι t0' := by
  have hyB : k⁻¹ * E.t * k ∈ E.B := E.conj_mem_B_of_mem_K hk E.t_mem_B
  have hy1 : k⁻¹ * E.t * k ≠ 1 := by
    intro h
    apply E.t_ne_one
    have : E.t = k * (k⁻¹ * E.t * k) * k⁻¹ := by group
    rw [this, h]
    group
  have hyz : k⁻¹ * E.t * k ∉ E.zK := fun h =>
    E.t_not_mem_zK hB.zK ((E.zK_inv_iff hk).2 h)
  obtain ⟨w, hw, hwy, hD⟩ := E.B_compl hB.zK hyB hy1 hyz
  rcases hD with h | h
  · rcases D2_A2 w hw h with rfl | rfl
    · exact Or.inl hwy.symm
    · exact Or.inr hwy.symm
  · exact absurd hwy.symm (hcon k hk w hw h)

theorem exists_tK_D3 [Finite G] (hB : E.CaseB) (hK : Nat.card E.K = 1152) :
    ∃ k ∈ E.K, ∃ w ∈ A2, D3 w = true ∧ k⁻¹ * E.t * k = E.ι w := by
  by_contra hcon'
  have hcon : ∀ k ∈ E.K, ∀ w ∈ A2, D3 w = true → k⁻¹ * E.t * k ≠ E.ι w := by
    intro k hk w hw h heq
    exact hcon' ⟨k, hk, w, hw, h, heq⟩
  have hsub : {y | ∃ k ∈ E.K, k⁻¹ * E.t * k = y} ⊆ {E.t, E.ι t0'} := by
    rintro _ ⟨k, hk, rfl⟩
    exact E.tK_cases hB hcon hk
  have hle : {y | ∃ k ∈ E.K, k⁻¹ * E.t * k = y}.ncard ≤ 2 := by
    calc _ ≤ ({E.t, E.ι t0'} : Set G).ncard := Set.ncard_le_ncard hsub (Set.toFinite _)
      _ ≤ 2 := by
        refine (Set.ncard_insert_le _ _).trans ?_
        rw [Set.ncard_singleton]
  have h := ncard_conjClass_mul_card E.K E.t
  rw [hK] at h
  have hC : E.K ⊓ Subgroup.centralizer ({E.t} : Set G) ≤ T := by
    rintro k ⟨hkK, hkC⟩
    have hkt : E.t * k = k * E.t := Subgroup.mem_centralizer_iff.mp hkC E.t rfl
    have hs : E.s ∈ E.K := E.T_le_K E.s_mem_T
    have ht' : E.ι t0' = E.s⁻¹ * E.t * E.s := by
      rw [t0'_eq_conj, map_mul, map_mul, map_inv]
      rfl
    have hk' : k⁻¹ * E.ι t0' * k = E.ι t0' := by
      have hcl : (E.s * k)⁻¹ * E.t * (E.s * k) = k⁻¹ * E.ι t0' * k := by rw [ht']; group
      rcases E.tK_cases hB hcon (E.K.mul_mem hs hkK) with h1 | h1
      · exfalso
        rw [hcl] at h1
        have h2 : E.ι t0' = k * E.t * k⁻¹ := by
          calc E.ι t0' = k * (k⁻¹ * E.ι t0' * k) * k⁻¹ := by group
            _ = k * E.t * k⁻¹ := by rw [h1]
        have h3 : k * E.t * k⁻¹ = E.t := by
          calc k * E.t * k⁻¹ = (E.t * k) * k⁻¹ := by rw [hkt]
            _ = E.t := by group
        exact t0'_ne_t0 (E.injective (h2.trans h3))
      · rw [← hcl]
        exact h1
    have hkt' : E.ι t0' * k = k * E.ι t0' := by
      calc E.ι t0' * k = k * (k⁻¹ * E.ι t0' * k) := by group
        _ = k * E.ι t0' := by rw [hk']
    have hz : k * E.z = E.z * k := by
      have hzeq : E.z = E.t * E.ι t0' := by
        rw [t, ← map_mul, t0_mul_t0']; rfl
      rw [hzeq]
      calc k * (E.t * E.ι t0') = (k * E.t) * E.ι t0' := by group
        _ = (E.t * k) * E.ι t0' := by rw [hkt]
        _ = E.t * (k * E.ι t0') := by group
        _ = E.t * (E.ι t0' * k) := by rw [hkt']
        _ = E.t * E.ι t0' * k := by group
    have hkz : k ∈ Subgroup.centralizer ({E.z} : Set G) :=
      Subgroup.mem_centralizer_iff.mpr fun h hh => by
        rw [Set.mem_singleton_iff] at hh
        subst hh
        exact hz.symm
    rw [hB.gz] at hkz
    exact hkz
  have hcle : Nat.card ↥(E.K ⊓ Subgroup.centralizer ({E.t} : Set G)) ≤ 128 := by
    rw [← E.card_T]
    exact Subgroup.card_le_of_le hC
  have hmul := Nat.mul_le_mul hle hcle
  omega

theorem tG_of_D23 [Finite G] (hB : E.CaseB) (hK : Nat.card E.K = 1152) {w : Wc}
    (hw : D2 w = true ∨ D3 w = true) : ∃ g : G, g⁻¹ * E.t * g = E.ι w := by
  rcases hw with h | h
  · obtain ⟨v, hv⟩ := (cls_t0 w).2 h
    refine ⟨E.ι v, ?_⟩
    rw [← hv]
    simp [t]
  · obtain ⟨v, hv⟩ := D3_into_B w h
    obtain ⟨k, hk, w₀, hw₀, hD₀, hkw₀⟩ := E.exists_tK_D3 hB hK
    obtain ⟨x, hx, hxw⟩ := B_orbit_D3 w₀ hw₀ hD₀ (v⁻¹ * w * v) hv (D3_conj h v)
    refine ⟨k * E.ι x * (E.ι v)⁻¹, ?_⟩
    have h1 : E.ι (v⁻¹ * w * v) = (k * E.ι x)⁻¹ * E.t * (k * E.ι x) := by
      rw [← hxw, map_mul, map_mul, map_inv, ← hkw₀]
      group
    calc (k * E.ι x * (E.ι v)⁻¹)⁻¹ * E.t * (k * E.ι x * (E.ι v)⁻¹)
        = E.ι v * ((k * E.ι x)⁻¹ * E.t * (k * E.ι x)) * (E.ι v)⁻¹ := by group
      _ = E.ι v * E.ι (v⁻¹ * w * v) * (E.ι v)⁻¹ := by rw [h1]
      _ = E.ι w := by rw [map_mul, map_mul, map_inv]; group

theorem exists_conj_s_mem_J [Finite G] (hG : IsSimpleGroup G) (hT : quasithinIsSylowTwo T) :
    ∃ x : G, x⁻¹ * E.s * x ∈ E.J := by
  by_contra hcon
  push Not at hcon
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨S, hS⟩ := exists_sylow_of_quasithinIsSylowTwo hT
  have hQP : E.J ≤ (S : Subgroup G) := hS ▸ E.J_le_T
  have hidx : E.J.relIndex (S : Subgroup G) = 2 := hS ▸ E.relIndex_J_T
  have hnot := thompson_transfer_lemma S hQP hidx E.orderOf_s hcon
  have htop : pResidual 2 G = ⊤ :=
    pResidual_two_eq_top hG (c := E.ι x3) (by rw [← map_pow, x3_cube, map_one])
      (fun h => x3_ne_one (E.injective (by rw [map_one]; exact h)))
  rw [htop] at hnot
  exact hnot (Subgroup.mem_top _)

theorem s_conj_t [Finite G] (hG : IsSimpleGroup G) (hB : E.CaseB) (hK : Nat.card E.K = 1152) :
    ∃ g : G, g⁻¹ * E.s * g = E.t := by
  obtain ⟨x, hx⟩ := E.exists_conj_s_mem_J hG hB.sylow
  obtain ⟨w₁, hw₁J, hw₁⟩ := Subgroup.mem_map.mp hx
  have hw₁1 : w₁ ≠ 1 := by
    rintro rfl
    rw [map_one] at hw₁
    apply s0_ne_one
    apply E.injective
    rw [map_one]
    calc E.ι s0 = x * (x⁻¹ * E.s * x) * x⁻¹ := by rw [s]; group
      _ = 1 := by rw [← hw₁]; group
  have hw₁2 : w₁ * w₁ = 1 := by
    apply E.injective
    rw [map_mul, hw₁, map_one]
    calc x⁻¹ * E.s * x * (x⁻¹ * E.s * x) = x⁻¹ * (E.s * E.s) * x := by group
      _ = 1 := by rw [E.s_sq]; group
  rcases involution_partition w₁ hw₁2 hw₁1 with h | h | h | h | h | h
  · exfalso
    obtain ⟨g, hg⟩ := E.zG_of_D145 hB.zK (Or.inl h)
    exact E.not_mem_zG_of_D236 hB.gz hB.sylow (w := s0) (Or.inr (Or.inr D6_s0))
      ⟨g * x⁻¹, by
        calc (g * x⁻¹)⁻¹ * E.z * (g * x⁻¹) = x * (g⁻¹ * E.z * g) * x⁻¹ := by group
          _ = x * (x⁻¹ * E.s * x) * x⁻¹ := by rw [hg, hw₁]
          _ = E.ι s0 := by rw [s]; group⟩
  · obtain ⟨g, hg⟩ := E.tG_of_D23 hB hK (Or.inl h)
    refine ⟨(g * x⁻¹)⁻¹, ?_⟩
    calc (g * x⁻¹)⁻¹⁻¹ * E.s * (g * x⁻¹)⁻¹ = g * (x⁻¹ * E.s * x) * g⁻¹ := by group
      _ = g * E.ι w₁ * g⁻¹ := by rw [hw₁]
      _ = g * (g⁻¹ * E.t * g) * g⁻¹ := by rw [hg]
      _ = E.t := by group
  · obtain ⟨g, hg⟩ := E.tG_of_D23 hB hK (Or.inr h)
    refine ⟨(g * x⁻¹)⁻¹, ?_⟩
    calc (g * x⁻¹)⁻¹⁻¹ * E.s * (g * x⁻¹)⁻¹ = g * (x⁻¹ * E.s * x) * g⁻¹ := by group
      _ = g * E.ι w₁ * g⁻¹ := by rw [hw₁]
      _ = g * (g⁻¹ * E.t * g) * g⁻¹ := by rw [hg]
      _ = E.t := by group
  · exfalso
    obtain ⟨g, hg⟩ := E.zG_of_D145 hB.zK (Or.inr (Or.inl h))
    exact E.not_mem_zG_of_D236 hB.gz hB.sylow (w := s0) (Or.inr (Or.inr D6_s0))
      ⟨g * x⁻¹, by
        calc (g * x⁻¹)⁻¹ * E.z * (g * x⁻¹) = x * (g⁻¹ * E.z * g) * x⁻¹ := by group
          _ = x * (x⁻¹ * E.s * x) * x⁻¹ := by rw [hg, hw₁]
          _ = E.ι s0 := by rw [s]; group⟩
  · exfalso
    obtain ⟨g, hg⟩ := E.zG_of_D145 hB.zK (Or.inr (Or.inr h))
    exact E.not_mem_zG_of_D236 hB.gz hB.sylow (w := s0) (Or.inr (Or.inr D6_s0))
      ⟨g * x⁻¹, by
        calc (g * x⁻¹)⁻¹ * E.z * (g * x⁻¹) = x * (g⁻¹ * E.z * g) * x⁻¹ := by group
          _ = x * (x⁻¹ * E.s * x) * x⁻¹ := by rw [hg, hw₁]
          _ = E.ι s0 := by rw [s]; group⟩
  · exact absurd hw₁J (D6_not_mem_Jh h)

theorem false_of_caseB [Finite G] (hG : IsSimpleGroup G) (hB : E.CaseB) (hK : Nat.card E.K = 1152)
    {c : G} (hcK : c ∈ E.K) (hcY : c ∈ E.Y) (hc3 : orderOf c = 3) : False := by
  obtain ⟨g', hg'⟩ := E.s_conj_t hG hB hK
  have hT₂ := E.T₂_le_X hB.sylow hB.gz hB.zK hcK hcY hc3
  have htX := E.t_not_mem_X hB hT₂
  obtain ⟨a, b, ha, hb, hab⟩ := exists_diag_odd_product
  have hu : ∀ v : G, v * E.s = E.s * v → v ^ 3 = 1 → g'⁻¹ * v * g' ∈ E.X := by
    intro v hvs hv3
    have hY : g'⁻¹ * v * g' ∈ E.Y := by
      rw [E.mem_Y, ← hg']
      calc g'⁻¹ * v * g' * (g'⁻¹ * E.s * g') = g'⁻¹ * (v * E.s) * g' := by group
        _ = g'⁻¹ * (E.s * v) * g' := by rw [hvs]
        _ = g'⁻¹ * E.s * g' * (g'⁻¹ * v * g') := by group
    have h3 : (g'⁻¹ * v * g') ^ 3 = 1 := by
      have : (g'⁻¹ * v * g') ^ 3 = g'⁻¹ * v ^ 3 * g' := by
        simp only [pow_succ, pow_zero, one_mul]
        group
      rw [this, hv3]
      group
    exact E.mem_X_of_odd hY (Odd.of_dvd_nat (by decide) (orderOf_dvd_of_pow_eq_one h3))
  have hdiag : ∀ x : S4, x * x * x = 1 →
      E.ι ⟨x, x, false⟩ * E.s = E.s * E.ι ⟨x, x, false⟩ ∧ E.ι ⟨x, x, false⟩ ^ 3 = 1 := by
    intro x hx
    refine ⟨?_, ?_⟩
    · rw [s, ← map_mul, ← map_mul, diag_commute_s0]
    · rw [← map_pow, diag_pow_three x hx, map_one]
  have hu₁ := hu _ (hdiag a ha).1 (hdiag a ha).2
  have hu₂ := hu _ (hdiag b hb).1 (hdiag b hb).2
  have huX : g'⁻¹ * E.ι ⟨a, a, false⟩ * g' * (g'⁻¹ * E.ι ⟨b, b, false⟩ * g') ∈ E.X :=
    E.X.mul_mem hu₁ hu₂
  have hq : E.ι ⟨a, a, false⟩ * E.ι ⟨b, b, false⟩ = E.ι ⟨v2, v2, false⟩ := by
    rw [← map_mul, diag_mul, hab]
  have hueq : g'⁻¹ * E.ι ⟨a, a, false⟩ * g' * (g'⁻¹ * E.ι ⟨b, b, false⟩ * g') =
      g'⁻¹ * E.ι ⟨v2, v2, false⟩ * g' := by
    rw [← hq]
    group
  rw [hueq] at huX
  have hu2 : (g'⁻¹ * E.ι ⟨v2, v2, false⟩ * g') * (g'⁻¹ * E.ι ⟨v2, v2, false⟩ * g') = 1 := by
    calc g'⁻¹ * E.ι ⟨v2, v2, false⟩ * g' * (g'⁻¹ * E.ι ⟨v2, v2, false⟩ * g')
        = g'⁻¹ * (E.ι ⟨v2, v2, false⟩ * E.ι ⟨v2, v2, false⟩) * g' := by group
      _ = 1 := by rw [← map_mul, q_sq, map_one]; group
  obtain ⟨h, hhY, hhJ⟩ := exists_conj_mem_of_sq (E.isSylowTwoOf_J hB.sylow hB.maxLocal)
    (E.X_le_Y huX) hu2
  have hu'X : h⁻¹ * (g'⁻¹ * E.ι ⟨v2, v2, false⟩ * g') * h ∈ E.X := by
    have := E.conj_mem_X (E.Y.inv_mem hhY) huX
    simpa using this
  have hT₂mem := E.J_inf_X hB hT₂ htX hhJ hu'X
  obtain ⟨w₂, hw₂, hw₂eq⟩ := Subgroup.mem_map.mp hT₂mem
  have hw₂1 : w₂ ≠ 1 := by
    rintro rfl
    rw [map_one] at hw₂eq
    apply q_ne_one
    apply E.injective
    rw [map_one]
    calc E.ι ⟨v2, v2, false⟩ = g' * (h * (h⁻¹ * (g'⁻¹ * E.ι ⟨v2, v2, false⟩ * g') * h) * h⁻¹) * g'⁻¹ := by
          group
      _ = 1 := by rw [← hw₂eq]; group
  have hw₂2 : w₂ * w₂ = 1 := by
    apply E.injective
    rw [map_mul, hw₂eq, map_one]
    calc h⁻¹ * (g'⁻¹ * E.ι ⟨v2, v2, false⟩ * g') * h * (h⁻¹ * (g'⁻¹ * E.ι ⟨v2, v2, false⟩ * g') * h)
        = h⁻¹ * ((g'⁻¹ * E.ι ⟨v2, v2, false⟩ * g') * (g'⁻¹ * E.ι ⟨v2, v2, false⟩ * g')) * h := by
          group
      _ = 1 := by rw [hu2]; group
  have hD := T2h_involution w₂ hw₂ hw₂2 hw₂1
  obtain ⟨m, hm⟩ := (cls_z0 ⟨v2, v2, false⟩).2 D1_v2_v2
  have hzm : (E.ι m)⁻¹ * E.z * E.ι m = E.ι ⟨v2, v2, false⟩ := by
    rw [← hm, map_mul, map_mul, map_inv]
    rfl
  have hno : ¬ ∃ g : G, g⁻¹ * E.z * g = E.ι w₂ := by
    rcases hD with hD | hD
    · exact E.not_mem_zG_of_D236 hB.gz hB.sylow (Or.inl hD)
    · exact E.not_mem_zG_of_D236 hB.gz hB.sylow (Or.inr (Or.inl hD))
  apply hno
  refine ⟨E.ι m * g' * h, ?_⟩
  rw [hw₂eq, ← hzm]
  group

end Emb

end CFSG.Quasithin.A10
