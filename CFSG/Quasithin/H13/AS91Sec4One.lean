module

public import CFSG.Quasithin.H13.AS91Sec4Setting
public import CFSG.GF2Type.Smith1979.IdxFourHLift
public import CFSG.GF2Type.Smith1979.IdxFourIdentFrattini

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Quasithin.H13.AS91

open Subgroup CFSG.Open CFSG.LargeExtraspecial CFSG.Quasithin CFSG.Quasithin.HatM22 Module
open CFSG.GF2Type.Smith1979.IdxFour
open CFSG.CharacterTheory.SteinbergBY (FieldFour)

variable {G : Type} [Group G] [Finite G] {S : Setting G} {θ : S.O} {c : S.M}

theorem exists_mul_zpow_of_mem_pre (hc : S.ρ c = θ) {g : G} (hg : g ∈ pre S (zpowers θ)) :
    ∃ q ∈ S.QG, ∃ k : ℤ, g = q * (c : G) ^ k := by
  obtain ⟨hgM, k, hk⟩ := mem_pre.mp hg
  have hk' : θ ^ k = S.ρ ⟨g, hgM⟩ := hk
  refine ⟨g * ((c : G) ^ k)⁻¹, ?_, k, by group⟩
  have h1 : S.ρ (⟨g, hgM⟩ * (c ^ k)⁻¹) = 1 := by
    rw [map_mul, map_inv, map_zpow, hc, hk', mul_inv_cancel]
  exact (S.ρ_eq_one_iff _).mp h1

theorem sup_eq_pre (hc : S.ρ c = θ) : S.QG ⊔ zpowers (c : G) = pre S (zpowers θ) := by
  apply le_antisymm
  · refine sup_le (QG_le_pre _) ?_
    rw [zpowers_le]
    exact mem_pre_of_rho c (by rw [hc]; exact mem_zpowers θ)
  · intro g hg
    obtain ⟨q, hq, k, rfl⟩ := exists_mul_zpow_of_mem_pre hc hg
    exact mul_mem_sup hq (zpow_mem (mem_zpowers _) k)

theorem conj_mem_pre {K : Subgroup S.O} (hK : ∀ m ∈ S.Mbar, ∀ k ∈ K, m * k * m⁻¹ ∈ K)
    {h : G} (hh : h ∈ S.M) {y : G} (hy : y ∈ pre S K) : h * y * h⁻¹ ∈ pre S K := by
  obtain ⟨hyM, hyK⟩ := mem_pre.mp hy
  have hM : h * y * h⁻¹ ∈ S.M := mul_mem (mul_mem hh hyM) (inv_mem hh)
  refine mem_pre.mpr ⟨hM, ?_⟩
  have e : (⟨h * y * h⁻¹, hM⟩ : S.M) = ⟨h, hh⟩ * ⟨y, hyM⟩ * ⟨h, hh⟩⁻¹ := rfl
  rw [e, map_mul, map_mul, map_inv]
  exact hK _ (MonoidHom.mem_range.mpr ⟨_, rfl⟩) _ hyK

theorem zpowers_normalized (hθn : ∀ m ∈ S.Mbar, m * θ * m⁻¹ ∈ zpowers θ) :
    ∀ m ∈ S.Mbar, ∀ k ∈ zpowers θ, m * k * m⁻¹ ∈ zpowers θ := by
  rintro m hm _ ⟨j, rfl⟩
  show m * θ ^ j * m⁻¹ ∈ zpowers θ
  rw [← conj_zpow]
  exact zpow_mem (hθn m hm) j

theorem factorization_three_mul_two_pow : (3 * 2 ^ 13 : ℕ).factorization 3 = 1 := by
  have h1 := (Nat.prime_three.pow_dvd_iff_le_factorization (by norm_num : (3 * 2 ^ 13 : ℕ) ≠ 0)).1
    (by norm_num : 3 ^ 1 ∣ 3 * 2 ^ 13)
  have h2 : ¬ 2 ≤ (3 * 2 ^ 13 : ℕ).factorization 3 := fun h =>
    absurd ((Nat.prime_three.pow_dvd_iff_le_factorization (by norm_num : (3 * 2 ^ 13 : ℕ) ≠ 0)).2 h)
      (by norm_num)
  omega

theorem M_eq_sup_normalizer (hc : S.ρ c = θ) (hc3 : orderOf (c : G) = 3) (hθ : θ ∈ S.Mbar)
    (hθ3 : orderOf θ = 3) (hθn : ∀ m ∈ S.Mbar, m * θ * m⁻¹ ∈ zpowers θ)
    (hQ : Nat.card S.QG = 2 ^ 13) :
    S.M = S.QG ⊔ (S.M ⊓ normalizer (zpowers (c : G) : Set G)) := by
  refine le_antisymm (fun x hx => ?_) (sup_le S.QG_le_M inf_le_left)
  have hE : Nat.card (pre S (zpowers θ)) = 3 * 2 ^ 13 := by
    rw [card_pre (zpowers_le.mpr hθ), Nat.card_zpowers, hθ3, hQ]
  obtain ⟨e, he, n, hn, hnA, rfl⟩ := frattini_of_normalizes S.M (pre S (zpowers θ))
    (zpowers (c : G)) (zpowers (c : G)) (pre_le_M _)
    (fun x hx e he => conj_mem_pre (zpowers_normalized hθn) hx he)
    (by rw [← sup_eq_pre hc]; exact le_sup_right)
    (by rw [hE, factorization_three_mul_two_pow, Nat.card_zpowers, hc3, pow_one])
    (fun _ _ h => h) x hx
  obtain ⟨q, hq, k, rfl⟩ := exists_mul_zpow_of_mem_pre hc he
  rw [mul_assoc]
  refine mul_mem_sup hq ⟨mul_mem (zpow_mem c.2 k) hn, mul_mem ?_ (mem_normalizer_fintype hnA)⟩
  exact le_normalizer (zpow_mem (mem_zpowers _) k)

theorem self_mem_cMbar (hθ : θ ∈ S.Mbar) : (θ : S.Qt ≃ₗ[ZMod 2] S.Qt) ∈ cMbar S θ :=
  mem_cMbar.mpr ⟨θ, hθ, rfl, rfl⟩

theorem self_mem_center_cMbar (hθ : θ ∈ S.Mbar) :
    (⟨θ, self_mem_cMbar hθ⟩ : ↥(cMbar S θ)) ∈ center ↥(cMbar S θ) := by
  rw [mem_center_iff]
  rintro ⟨g, hg⟩
  obtain ⟨m, -, hmθ, rfl⟩ := mem_cMbar.mp hg
  apply Subtype.ext
  change (m : S.Qt ≃ₗ[ZMod 2] S.Qt) * θ = θ * m
  rw [← Subgroup.coe_mul, ← Subgroup.coe_mul, hmθ]

theorem inf_centralizer_eq (hHat : HatM22SmallModules) (hw : S.width = 6) (hc : S.ρ c = θ)
    (hθ : θ ∈ S.Mbar) (hθ1 : θ ≠ 1)
    (hL : IsHat ↥(cMbar S θ) (CFSG.Blueprint.NativeSporadic.Carrier .M22)) :
    S.QG ⊓ centralizer (zpowers (c : G) : Set G) = zpowers S.z := by
  apply le_antisymm
  · rintro q ⟨hq, hqc⟩
    have hcq : (c : G) * q = q * c := mem_centralizer_iff.mp hqc c (mem_zpowers _)
    have hfix : ((θ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl q) = S.cl q := by
      rw [← hc, S.ρ_cl c hq, hcq, mul_inv_cancel_right]
    have hne : (⟨θ, self_mem_cMbar hθ⟩ : ↥(cMbar S θ)) ≠ 1 := by
      intro h1
      apply hθ1
      apply Subtype.ext
      have h2 := congrArg Subtype.val h1
      exact h2
    have hU : finrank (ZMod 2) S.Qt = 12 := by rw [S.finrank_Qt_eq_two_mul_width, hw]
    haveI : Finite S.Qt := Module.finite_of_finite (ZMod 2)
    have h0 := center_fixedPointFree hHat hU (cMbar S θ) hL (self_mem_center_cMbar hθ) hne
      (S.cl q) hfix
    rcases (S.cl_eq_zero_iff hq).mp h0 with rfl | rfl
    · exact one_mem _
    · exact mem_zpowers _
  · rw [zpowers_le]
    refine ⟨S.z_mem_QG, mem_centralizer_iff.mpr ?_⟩
    rintro y ⟨k, rfl⟩
    exact (Commute.zpow_left (S.z_comm c.2) k).eq

theorem rho_mem_cMbar (hc : S.ρ c = θ) {h : S.M}
    (hh : (h : G) ∈ centralizer (zpowers (c : G) : Set G)) :
    ((S.ρ h : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) ∈ cMbar S θ := by
  refine mem_cMbar.mpr ⟨S.ρ h, MonoidHom.mem_range.mpr ⟨h, rfl⟩, ?_, rfl⟩
  have hch : (c : G) * h = h * c := mem_centralizer_iff.mp hh c (mem_zpowers _)
  rw [← hc, ← map_mul, ← map_mul]
  exact congrArg S.ρ (Subtype.ext hch.symm)

theorem exists_centralizer_of_mem_cMbar (hc3 : c ^ 3 = 1) (hc : S.ρ c = θ)
    {g : S.Qt ≃ₗ[ZMod 2] S.Qt} (hg : g ∈ cMbar S θ) :
    ∃ h : S.M, (h : G) ∈ centralizer (zpowers (c : G) : Set G) ∧
      ((S.ρ h : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) = g := by
  obtain ⟨m, hmM, hmθ, rfl⟩ := mem_cMbar.mp hg
  obtain ⟨s, hs, hcs⟩ := exists_comm_lift hc3 hmM (by rw [hc]; exact hmθ.symm)
  refine ⟨s, mem_centralizer_iff.mpr ?_, by rw [hs]⟩
  rintro y ⟨k, rfl⟩
  exact (Commute.zpow_left (show Commute (c : G) s from congrArg Subtype.val hcs) k).eq

structure Data41 {G : Type} [Group G] [Finite G] {z : G} (h : HypJ4 G z) where
  θ : h.setting.O
  θ_mem : θ ∈ h.setting.Mbar
  θ_pow : θ ^ 3 = 1
  θ_ne : θ ≠ 1
  θ_normal : ∀ m ∈ h.setting.Mbar, m * θ * m⁻¹ ∈ zpowers θ
  hat : IsHat ↥(cMbar h.setting θ) (CFSG.Blueprint.NativeSporadic.Carrier .M22)
  outer : ∃ τ ∈ h.setting.Mbar, τ * θ ≠ θ * τ
  card_Mbar : Nat.card h.setting.Mbar = 2661120
  c : h.setting.M
  c_pow : c ^ 3 = 1
  ρ_c : h.setting.ρ c = θ
  ψ : h.setting.Qt ≃+ (Fin 6 → FieldFour)
  ψ_acts : ∀ g ∈ cMbar h.setting θ, ∃ γ ∈ hatM22Γ₀, ∀ v : h.setting.Qt,
    ψ (g v) = ((γ : Matrix.GeneralLinearGroup (Fin 6) FieldFour) :
      Matrix (Fin 6) (Fin 6) FieldFour).mulVec (ψ v)
  ψ_onto : ∀ γ ∈ hatM22Γ₀, ∃ g ∈ cMbar h.setting θ, ∀ v : h.setting.Qt,
    ψ (g v) = ((γ : Matrix.GeneralLinearGroup (Fin 6) FieldFour) :
      Matrix (Fin 6) (Fin 6) FieldFour).mulVec (ψ v)

theorem HypJ4.nonempty_data41 (hHat : HatM22SmallModules) {z : G}
    (h : HypJ4 G z) : Nonempty (Data41 h) := by
  obtain ⟨θ, hθM, hθ3, hθ1, hθn, hL, hτ, hcard⟩ := h.exists_center_gen
  obtain ⟨c, hc3, hc⟩ := exists_pow3_lift hθM hθ3
  have hU : finrank (ZMod 2) h.setting.Qt = 12 := by
    rw [h.setting.finrank_Qt_eq_two_mul_width, h.setting_width]
  haveI : Finite h.setting.Qt := Module.finite_of_finite (ZMod 2)
  obtain ⟨ψ, hψ1, hψ2⟩ := exists_hatM22_realization hHat hU (cMbar h.setting θ) hL
  exact ⟨⟨θ, hθM, hθ3, hθ1, hθn, hL, hτ, hcard, c, hc3, hc, ψ, hψ1, hψ2⟩⟩

variable {z : G} {h : HypJ4 G z}

theorem Data41.c_ne (D : Data41 h) : (D.c : G) ≠ 1 := fun h1 =>
  D.θ_ne (by rw [← D.ρ_c, show D.c = 1 from Subtype.ext h1, map_one])

theorem Data41.orderOf_c (D : Data41 h) : orderOf (D.c : G) = 3 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  exact orderOf_eq_prime (by rw [← Subgroup.coe_pow, D.c_pow, Subgroup.coe_one]) D.c_ne

theorem Data41.orderOf_θ (D : Data41 h) : orderOf D.θ = 3 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  exact orderOf_eq_prime D.θ_pow D.θ_ne

theorem Data41.card_QG (D : Data41 h) : Nat.card h.setting.QG = 2 ^ 13 := by
  rw [h.setting.card_QG_eq_card_Q, h.setting.card_Q_eq, h.setting_width]

@[expose] noncomputable def Data41.toLoc41 (D : Data41 h) (hHat : HatM22SmallModules) :
    Loc41 G z where
  S := h.setting
  S_z := h.setting_z
  S_QG := h.setting_QG
  X := zpowers (D.c : G)
  X_le := zpowers_le.mpr D.c.2
  card_X := by rw [Nat.card_zpowers, D.orderOf_c]
  QX_normal := by
    rw [← h.setting_QG, sup_eq_pre D.ρ_c]
    exact fun x hx y hy => conj_mem_pre (zpowers_normalized D.θ_normal) hx hy
  eq_sup_normalizer := by
    have hFr := M_eq_sup_normalizer D.ρ_c D.orderOf_c D.θ_mem D.orderOf_θ D.θ_normal D.card_QG
    rwa [h.setting_QG] at hFr
  inf_centralizer := by
    have hCQ := inf_centralizer_eq hHat h.setting_width D.ρ_c D.θ_mem D.θ_ne D.hat
    rwa [h.setting_QG] at hCQ
  ψ := D.ψ
  acts := fun m hm => D.ψ_acts _ (rho_mem_cMbar D.ρ_c hm)
  onto := fun γ hγ => by
    obtain ⟨g, hg, hgv⟩ := D.ψ_onto γ hγ
    obtain ⟨m, hm, hmg⟩ := exists_centralizer_of_mem_cMbar D.c_pow D.ρ_c hg
    exact ⟨m, hm, fun v => by rw [hmg]; exact hgv v⟩

end CFSG.Quasithin.H13.AS91
