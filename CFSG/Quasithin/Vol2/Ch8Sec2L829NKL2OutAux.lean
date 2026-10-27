module

public import CFSG.LocalAnalysis.ComponentClassification.AutL2FactsHarrisBase

public section

namespace CFSG.Quasithin.H13.L829NK.L2Out

open CFSG CFSG.ComponentClassification.AutL2Facts GorensteinWalter Subgroup

theorem fu_val {F : Type} [Field F] (σ : F ≃+* F) (a : Fˣ) :
    ((fu F σ a : Fˣ) : F) = σ (a : F) := rfl

theorem field_part_eq_one {F : Type} [Field F] (h2 : (2 : F) ≠ 0) (hsq : IsSquare (-1 : F))
    (h15 : (15 : F) ≠ 0) (ε : Bool) (σ : F ≃+* F)
    (hT : ∀ u : Fˣ, twist F ε (fu F σ (u * u)) = u * u) : σ = 1 := by
  cases ε with
  | false =>
    have hσ : ∀ z : F, σ (z * z) = z * z := by
      intro z
      by_cases hz : z = 0
      · subst hz
        simp
      · have h : fu F σ (Units.mk0 z hz * Units.mk0 z hz) = Units.mk0 z hz * Units.mk0 z hz := by
          have := hT (Units.mk0 z hz)
          rwa [twist_false] at this
        have h' := congrArg (fun w : Fˣ => (w : F)) h
        simp only [fu_val, Units.val_mul, Units.val_mk0] at h'
        exact h'
    obtain ⟨r, hr⟩ := hsq
    obtain ⟨t, ht⟩ : ∃ t : F, 2 * t = 1 := ⟨(2 : F)⁻¹, mul_inv_cancel₀ h2⟩
    have hx : ∀ x : F, σ x = x := by
      intro x
      have key : x = ((x + 1) * t) * ((x + 1) * t) + (r * ((x - 1) * t)) * (r * ((x - 1) * t)) := by
        linear_combination (-x * (2 * t + 1)) * ht + ((x - 1) ^ 2 * t ^ 2) * hr
      calc σ x = σ (((x + 1) * t) * ((x + 1) * t) + (r * ((x - 1) * t)) * (r * ((x - 1) * t))) := by
            rw [← key]
        _ = σ (((x + 1) * t) * ((x + 1) * t)) + σ ((r * ((x - 1) * t)) * (r * ((x - 1) * t))) :=
            map_add σ _ _
        _ = ((x + 1) * t) * ((x + 1) * t) + (r * ((x - 1) * t)) * (r * ((x - 1) * t)) := by
            rw [hσ, hσ]
        _ = x := key.symm
    exact RingEquiv.ext hx
  | true =>
    exfalso
    have h : (fu F σ (Units.mk0 2 h2 * Units.mk0 2 h2))⁻¹ = Units.mk0 2 h2 * Units.mk0 2 h2 := by
      have := hT (Units.mk0 2 h2)
      rwa [twist_true] at this
    have h' : fu F σ (Units.mk0 2 h2 * Units.mk0 2 h2) =
        (Units.mk0 2 h2 * Units.mk0 2 h2)⁻¹ := by
      calc fu F σ (Units.mk0 2 h2 * Units.mk0 2 h2)
          = ((fu F σ (Units.mk0 2 h2 * Units.mk0 2 h2))⁻¹)⁻¹ := (inv_inv _).symm
        _ = (Units.mk0 2 h2 * Units.mk0 2 h2)⁻¹ := by rw [h]
    have h3 := congrArg (fun w : Fˣ => (w : F)) h'
    simp only [fu_val, Units.val_mul, Units.val_mk0, Units.val_inv_eq_inv_val] at h3
    rw [map_mul, map_ofNat] at h3
    have h4 : (2 : F) * 2 ≠ 0 := mul_ne_zero h2 h2
    have h5 : ((2 : F) * 2) * ((2 : F) * 2)⁻¹ = 1 := mul_inv_cancel₀ h4
    rw [← h3] at h5
    apply h15
    linear_combination h5

theorem core {X : Type} [Group X] {F : Type} [Field F] [Finite F]
    (hodd : IsOddPrimePower (Nat.card F)) (φ : X ≃* PSL2 F) (Q : Sylow 2 X)
    (hQ8 : 8 ≤ Nat.card Q) (y : MulAut X) (hy : y * y = 1)
    (hfix : ∀ s ∈ (Q : Subgroup X), y s = s) (hr : (autEquiv φ y).right = 1) :
    ∃ x : X, y = MulAut.conj x := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Finite X := Finite.of_equiv _ φ.symm.toEquiv
  have hg2 : autEquiv φ y * autEquiv φ y = 1 := by rw [← map_mul, hy, map_one]
  have hk : autEquiv φ y ^ 2 ^ 1 = 1 := by rw [pow_one, sq]; exact hg2
  have hD8 : 8 ≤ Nat.card (sylowMap φ Q) := by rw [card_sylowMap]; exact hQ8
  have hgD : ∀ d ∈ (sylowMap φ Q : Subgroup (PSL2 F)),
      autEquiv φ y * incl F d = incl F d * autEquiv φ y := by
    intro d hd
    rw [coe_sylowMap] at hd
    obtain ⟨x, hx, rfl⟩ := hd
    exact (apply_eq_iff_commute φ y x).mp (hfix x hx)
  obtain ⟨d, -, hdg⟩ := Subgroup.mem_map.mp
    (mem_center_of_right_eq_one hodd (sylowMap φ Q) hD8 _ hr hk hgD)
  refine ⟨φ.symm d, ?_⟩
  apply (autEquiv φ).injective
  rw [autEquiv_conj, MulEquiv.apply_symm_apply]
  exact hdg.symm

theorem right_one_of_odd {X : Type} [Group X] {F : Type} [Field F] [Finite F] {p n : ℕ}
    (hp : p.Prime) (hF : Nat.card F = p ^ n) (hn : Odd n) (φ : X ≃* PSL2 F) (y : MulAut X)
    (hy : y * y = 1) : (autEquiv φ y).right = 1 := by
  have hg2 : autEquiv φ y * autEquiv φ y = 1 := by rw [← map_mul, hy, map_one]
  have hk : (autEquiv φ y).right ^ 2 ^ 1 = 1 := by
    have h := congrArg (fieldProj F) (show autEquiv φ y ^ 2 ^ 1 = 1 by
      rw [pow_one, sq]; exact hg2)
    rwa [map_pow, map_one] at h
  exact eq_one_of_two_power_ringAut hp hF hn _ 1 hk

theorem sq_mod_sixteen_of_mod_eight {m : ℕ} (hm : m % 8 = 1 ∨ m % 8 = 7) : m ^ 2 % 16 = 1 := by
  have h : m % 16 = 1 ∨ m % 16 = 7 ∨ m % 16 = 9 ∨ m % 16 = 15 := by omega
  rw [Nat.pow_mod]
  rcases h with h | h | h | h <;> simp [h]

theorem sq_mod_eight_of_odd {p : ℕ} (hp : p % 2 = 1) : p ^ 2 % 8 = 1 := by
  have h : p % 8 = 1 ∨ p % 8 = 3 ∨ p % 8 = 5 ∨ p % 8 = 7 := by omega
  rw [Nat.pow_mod]
  rcases h with h | h | h | h <;> simp [h]

theorem eight_dvd_card_PSL2 {K : Type} [Field K] [Finite K] (hodd : IsOddPrimePower (Nat.card K))
    (h16 : Nat.card K ^ 2 % 16 = 1) : 8 ∣ Nat.card (PSL2 K) := by
  rw [psl2_card_formula K hodd]
  obtain ⟨k, hk⟩ : ∃ k, Nat.card K ^ 2 - 1 = 16 * k := by
    refine ⟨(Nat.card K ^ 2 - 1) / 16, ?_⟩
    generalize Nat.card K ^ 2 = m at h16 ⊢
    omega
  rw [hk, show Nat.card K * (16 * k) = 2 * (8 * (Nat.card K * k)) by ring,
    Nat.mul_div_cancel_left _ two_pos]
  exact dvd_mul_right 8 _

theorem eight_le_card_sylow {X : Type} [Group X] [Finite X] (Q : Sylow 2 X)
    (h8 : 8 ∣ Nat.card X) : 8 ≤ Nat.card Q := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [Sylow.card_eq_multiplicity]
  have hX : Nat.card X ≠ 0 := (Nat.card_pos).ne'
  have h3 : 3 ≤ (Nat.card X).factorization 2 :=
    (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two hX).mp (by norm_num; exact h8)
  calc 8 = 2 ^ 3 := by norm_num
    _ ≤ 2 ^ (Nat.card X).factorization 2 := Nat.pow_le_pow_right (by norm_num) h3

theorem eq_one_or_eq_of_card_two_mem {G : Type} [Group G] [Finite G] (H : Subgroup G)
    (hH : Nat.card H = 2) {z : G} (hz : z ∈ H) (hz1 : z ≠ 1) {v : G} (hv : v ∈ H) :
    v = 1 ∨ v = z := by
  have hsub : ({1, z} : Set G) ⊆ (H : Set G) := by
    intro x hx
    rcases hx with rfl | rfl
    · exact H.one_mem
    · exact hz
  have hcard : (H : Set G).ncard = 2 := by
    rw [← Nat.card_coe_set_eq]
    exact hH
  have heq := Set.eq_of_subset_of_ncard_le hsub
    (by rw [hcard, Set.ncard_pair hz1.symm]) (Set.toFinite _)
  have hv' : v ∈ ({1, z} : Set G) := by
    rw [heq]
    exact hv
  simpa using hv'

theorem card_sylow_psl2 {F : Type} [Field F] [Finite F] (hodd : IsOddPrimePower (Nat.card F))
    (hq4 : Nat.card F % 4 = 1) (P : Sylow 2 (PSL2 F)) : Nat.card P = 2 ^ twoVal F := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [Sylow.card_eq_multiplicity, psl2_factorization_two hodd hq4]

theorem neg_one_mem_zpowers_stdGen_sq {F : Type} [Field F] [Finite F]
    (hodd : IsOddPrimePower (Nat.card F)) (h8 : 8 ≤ 2 ^ twoVal F) :
    (-1 : Fˣ) ∈ zpowers (stdGen F ^ 2) := by
  have htv : 3 ≤ twoVal F := by
    rcases Nat.lt_or_ge (twoVal F) 3 with h | h
    · have h' : twoVal F ≤ 2 := by omega
      have : 2 ^ twoVal F ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) h'
      omega
    · exact h
  have hx2 : (stdGen F ^ (2 ^ (twoVal F - 1))) ^ 2 = 1 := by
    rw [← pow_mul, ← pow_succ, Nat.sub_add_cancel (by omega : 1 ≤ twoVal F), ← orderOf_stdGen,
      pow_orderOf_eq_one]
  have hx1 : stdGen F ^ (2 ^ (twoVal F - 1)) ≠ 1 := by
    intro h1
    have hd := orderOf_dvd_of_pow_eq_one h1
    rw [orderOf_stdGen] at hd
    have := (Nat.pow_dvd_pow_iff_le_right (by norm_num : 1 < 2)).mp hd
    omega
  have hneg : stdGen F ^ (2 ^ (twoVal F - 1)) = -1 :=
    (units_eq_one_or_neg_one hx2).resolve_left hx1
  have hmem : (stdGen F ^ 2) ^ (2 ^ (twoVal F - 2)) = -1 := by
    rw [← hneg, ← pow_mul, ← pow_succ', show twoVal F - 2 + 1 = twoVal F - 1 by omega]
  rw [← hmem]
  exact pow_mem (mem_zpowers _) _

end CFSG.Quasithin.H13.L829NK.L2Out
