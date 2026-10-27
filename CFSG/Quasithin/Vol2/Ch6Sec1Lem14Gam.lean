module

public import CFSG.Quasithin.Vol2.Ch6Hyperplane
public import CFSG.Quasithin.Vol2.Ch6Offender

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique CFSG.Quasithin.E3
open scoped IsMulCommutative

section Field

variable {F : Type} [Field F] [Finite F]

theorem semilinear_line_comm (hF : 2 ∣ Nat.card F) {σ τ : F ≃+* F} {κ μ : F}
    (h1 : ∀ c, σ (σ c * κ) * κ = c) (h2 : ∀ c, τ (τ c * μ) * μ = c)
    (h12 : ∀ c, σ (τ c * μ) * κ = τ (σ c * κ) * μ)
    (hf : ∃ c, σ c * κ ≠ c) (hg : ∃ c, τ c * μ ≠ c) : ∀ c, σ (τ c * μ) * κ = c := by
  have : CharP F 2 := charP_two_of_two_dvd hF
  have h2F : (2 : F) = 0 := CharTwo.two_eq_zero
  have hsq : ∀ a : F, a * a = 1 → a = 1 := fun a ha => by
    have : (a - 1) * (a - 1) = 0 := by linear_combination ha - a * h2F + h2F
    exact sub_eq_zero.mp (mul_self_eq_zero.mp this)
  have hκ : σ κ * κ = 1 := by simpa using h1 1
  have hσ2 : ∀ c, σ (σ c) = c := fun c => by
    have := h1 c
    rw [map_mul, mul_assoc, hκ, mul_one] at this
    exact this
  have hμ : τ μ * μ = 1 := by simpa using h2 1
  have hτ2 : ∀ c, τ (τ c) = c := fun c => by
    have := h2 c
    rw [map_mul, mul_assoc, hμ, mul_one] at this
    exact this
  have hσ1 : σ ≠ 1 := by
    intro h0
    obtain ⟨c, hc⟩ := hf
    have hκ1 : κ = 1 := hsq κ (by simpa [h0] using hκ)
    apply hc
    rw [h0, hκ1, mul_one]
    rfl
  have hτ1 : τ ≠ 1 := by
    intro h0
    obtain ⟨c, hc⟩ := hg
    have hμ1 : μ = 1 := hsq μ (by simpa [h0] using hμ)
    apply hc
    rw [h0, hμ1, mul_one]
    rfl
  have hστ : σ = τ := ringEquiv_eq_of_mul_self_eq_one hF (RingEquiv.ext hσ2) (RingEquiv.ext hτ2)
    hσ1 hτ1
  subst hστ
  have hfg : ∀ c, σ (σ c * μ) * κ = c * (σ μ * κ) := fun c => by
    rw [map_mul, hσ2]
    ring
  have e : ∀ c, σ (σ (σ (σ c * μ) * κ) * μ) * κ = c := by
    intro c
    rw [h12 (σ (σ c * μ) * κ), h1, h2]
  have hν : (σ μ * κ) * (σ μ * κ) = 1 := by
    have := e 1
    rw [hfg, hfg, one_mul] at this
    exact this
  have hν1 := hsq _ hν
  intro c
  rw [hfg, hν1, mul_one]

end Field

variable {G : Type} [Group G] [Finite G] {T M L V : Subgroup G} {n : ℕ}

namespace Hyp611Nat

theorem exists_conj_eq_smul_of_mem_normalizer_ZS (h : Hyp611Nat G T M L V n)
    {v : Fin 2 → h.data.K} (hv : v ≠ 0) (hle : h.rhoTL ≤ sl2Stab v) {x : G}
    (hxN : x ∈ Subgroup.normalizer (V : Set G))
    (hxZ : x ∈ Subgroup.normalizer (ch6ZS T L V : Set G)) :
    ∃ κ : h.data.K, h.data.conj ⟨x, hxN⟩ v = κ • v := by
  set z : ↥V := h.data.E.symm (Multiplicative.ofAdd v) with hzdef
  have hEz : Multiplicative.toAdd (h.data.E z) = v := by simp [hzdef]
  have hz : (z : G) ∈ ch6ZS T L V := (h.mem_ZS_iff_line hv hle z).mpr ⟨1, by rw [hEz, one_smul]⟩
  have hz' : ((conjAct V ⟨x, hxN⟩ z : ↥V) : G) ∈ ch6ZS T L V := by
    rw [conjAct_apply_coe]
    exact (Subgroup.mem_normalizer_iff.mp hxZ z).mp hz
  obtain ⟨κ, hκ⟩ := (h.mem_ZS_iff_line hv hle (conjAct V ⟨x, hxN⟩ z)).mp hz'
  refine ⟨κ, ?_⟩
  calc h.data.conj ⟨x, hxN⟩ v = h.data.conj ⟨x, hxN⟩ (Multiplicative.toAdd (h.data.E z)) := by
        rw [hEz]
    _ = Multiplicative.toAdd (h.data.E (conjAct V ⟨x, hxN⟩ z)) := h.data.conj_apply _ z
    _ = κ • v := hκ

theorem false_of_commuting_on_ZS (h : Hyp611Nat G T M L V n) {x y : G}
    (hxN : x ∈ Subgroup.normalizer (V : Set G)) (hyN : y ∈ Subgroup.normalizer (V : Set G))
    (hxL : x ∈ Subgroup.normalizer (L : Set G)) (hyL : y ∈ Subgroup.normalizer (L : Set G))
    (hxZ : x ∈ Subgroup.normalizer (ch6ZS T L V : Set G))
    (hyZ : y ∈ Subgroup.normalizer (ch6ZS T L V : Set G))
    (hx2 : ∀ z ∈ ch6ZS T L V, x * (x * z * x⁻¹) * x⁻¹ = z)
    (hy2 : ∀ z ∈ ch6ZS T L V, y * (y * z * y⁻¹) * y⁻¹ = z)
    (hxy : ∀ z ∈ ch6ZS T L V, x * (y * z * y⁻¹) * x⁻¹ = y * (x * z * x⁻¹) * y⁻¹)
    (hx1 : ∃ z ∈ ch6ZS T L V, x * z * x⁻¹ ≠ z) (hy1 : ∃ z ∈ ch6ZS T L V, y * z * y⁻¹ ≠ z)
    (hxy1 : ∃ z ∈ ch6ZS T L V, x * (y * z * y⁻¹) * x⁻¹ ≠ z) : False := by
  classical
  obtain ⟨v, hv, hle⟩ := h.exists_line
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hv
  simp only [Pi.zero_apply] at hi
  let zc : h.data.K → ↥V := fun c => h.data.E.symm (Multiplicative.ofAdd (c • v))
  have hzcE : ∀ c, Multiplicative.toAdd (h.data.E (zc c)) = c • v := fun c => by simp [zc]
  have hzcZ : ∀ c, ((zc c : ↥V) : G) ∈ ch6ZS T L V := fun c =>
    (h.mem_ZS_iff_line hv hle (zc c)).mpr ⟨c, hzcE c⟩
  have hzc_inj : ∀ c c', ((zc c : ↥V) : G) = zc c' → c = c' := by
    intro c c' hcc'
    have h1 := congrArg (fun z => Multiplicative.toAdd (h.data.E z)) (Subtype.ext hcc')
    simp only [hzcE] at h1
    have := congrFun h1 i
    simp only [Pi.smul_apply, smul_eq_mul] at this
    exact mul_right_cancel₀ hi this
  have hzc_surj : ∀ z ∈ ch6ZS T L V, ∃ c, z = ((zc c : ↥V) : G) := by
    intro z hz
    obtain ⟨c, hc⟩ := (h.mem_ZS_iff_line hv hle ⟨z, hz.1⟩).mp hz
    refine ⟨c, ?_⟩
    have : (⟨z, hz.1⟩ : ↥V) = zc c := h.data.E.injective (Multiplicative.toAdd.injective
      (by rw [hc, hzcE]))
    exact congrArg Subtype.val this
  have hact : ∀ {w : G} (hwN : w ∈ Subgroup.normalizer (V : Set G)),
      w ∈ Subgroup.normalizer (L : Set G) → w ∈ Subgroup.normalizer (ch6ZS T L V : Set G) →
      ∃ (σ : h.data.K ≃+* h.data.K) (κ : h.data.K), ∀ c,
        w * ((zc c : ↥V) : G) * w⁻¹ = ((zc (σ c * κ) : ↥V) : G) := by
    intro w hwN hwL hwZ
    obtain ⟨σ, hσ⟩ := h.data.exists_semilinear ⟨w, hwN⟩ hwL
    obtain ⟨κ, hκ⟩ := h.exists_conj_eq_smul_of_mem_normalizer_ZS hv hle hwN hwZ
    refine ⟨σ, κ, fun c => ?_⟩
    have h1 : Multiplicative.toAdd (h.data.E (conjAct V ⟨w, hwN⟩ (zc c))) =
        Multiplicative.toAdd (h.data.E (zc (σ c * κ))) := by
      rw [← h.data.conj_apply, hzcE, hσ, hκ, hzcE, smul_smul]
    have h2 := congrArg Subtype.val (h.data.E.injective (Multiplicative.toAdd.injective h1))
    rw [conjAct_apply_coe] at h2
    exact h2
  obtain ⟨σ, κ, hσκ⟩ := hact hxN hxL hxZ
  obtain ⟨τ, μ, hτμ⟩ := hact hyN hyL hyZ
  refine absurd ?_ (show ¬ ∀ z ∈ ch6ZS T L V, x * (y * z * y⁻¹) * x⁻¹ = z by
    push Not
    exact hxy1)
  have key := semilinear_line_comm h.two_dvd_card_K (σ := σ) (τ := τ) (κ := κ) (μ := μ)
    (fun c => hzc_inj _ _ (by rw [← hσκ, ← hσκ]; exact hx2 _ (hzcZ c)))
    (fun c => hzc_inj _ _ (by rw [← hτμ, ← hτμ]; exact hy2 _ (hzcZ c)))
    (fun c => hzc_inj _ _ (by rw [← hτμ, ← hσκ, ← hσκ, ← hτμ]; exact hxy _ (hzcZ c)))
    (by
      obtain ⟨z, hz, hz1⟩ := hx1
      obtain ⟨c, rfl⟩ := hzc_surj z hz
      exact ⟨c, fun h0 => hz1 (by rw [hσκ, h0])⟩)
    (by
      obtain ⟨z, hz, hz1⟩ := hy1
      obtain ⟨c, rfl⟩ := hzc_surj z hz
      exact ⟨c, fun h0 => hz1 (by rw [hτμ, h0])⟩)
  intro z hz
  obtain ⟨c, rfl⟩ := hzc_surj z hz
  rw [hτμ, hσκ, key]

end Hyp611Nat

end CFSG.Quasithin.H13
