module

public import CFSG.Quasithin.EmptyFaithful.SBc16GAct
public import CFSG.Quasithin.EmptyFaithful.SBc16GQuot

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7

namespace SBc16

theorem exists_sr_of_mul_self_eq_one {n : ℕ} [NeZero n] (hn : Odd n) {a : DihedralGroup n}
    (h1 : a ≠ 1) (h2 : a * a = 1) : ∃ i : ZMod n, a = DihedralGroup.sr i := by
  have h2' : ∀ x : ZMod n, x + x = 0 → x = 0 := by
    intro x hx
    have hu : IsUnit ((2 : ℕ) : ZMod n) :=
      (ZMod.isUnit_iff_coprime 2 n).mpr (Nat.coprime_two_left.mpr hn)
    have : ((2 : ℕ) : ZMod n) * x = 0 := by
      push_cast
      rw [two_mul]
      exact hx
    exact (hu.mul_right_eq_zero).mp this
  cases a with
  | r i =>
    exfalso
    apply h1
    have hi : i + i = 0 := by
      rw [DihedralGroup.r_mul_r, ← DihedralGroup.r_zero, DihedralGroup.r.injEq] at h2
      exact h2
    rw [h2' i hi, DihedralGroup.r_zero]
  | sr i => exact ⟨i, rfl⟩

section Elements

variable {G : Type} [Group G] [Finite G] {T M H : Subgroup G} {p : ℕ} {H₀ H₁ H₂ : Subgroup G} {t : G}

omit [Finite G] in
theorem reflection_conj_mem [NeZero p] (hp : Odd p) (h : IsDecP T M H p H₀ H₁ H₂ t) {s k : G}
    (hs : s ∈ H₁) (hss : s * s ∈ pCoreOf 2 H) (hsQ : s ∉ pCoreOf 2 H) (hk : k ∈ oTwoUpper H₁) :
    s * k * s⁻¹ * k ∈ pCoreOf 2 H := by
  obtain ⟨φ, -, hφ⟩ := h.exists_phiP
  obtain ⟨hkH, j, hj⟩ := IsDecP.mem_rotation (φ := φ) hk
  have h1 : φ ⟨s, hs⟩ ≠ 1 := fun hh => hsQ ((hφ _).mp hh)
  have h2 : φ ⟨s, hs⟩ * φ ⟨s, hs⟩ = 1 := by
    rw [← map_mul]
    exact (hφ _).mpr hss
  obtain ⟨i, hi⟩ := exists_sr_of_mul_self_eq_one hp h1 h2
  have h3 : φ (⟨s, hs⟩ * ⟨k, hkH⟩ * ⟨s, hs⟩⁻¹ * ⟨k, hkH⟩) = 1 := by
    rw [map_mul, map_mul, map_mul, map_inv, hi, hj, DihedralGroup.inv_sr, DihedralGroup.sr_mul_r,
      DihedralGroup.sr_mul_sr, DihedralGroup.r_mul_r, ← DihedralGroup.r_zero]
    congr 1
    ring
  exact (hφ _).mp h3

theorem actHom_fix_V₂ (h : IsDecP T M H p H₀ H₁ H₂ t) {s : G} (hs : s ∈ H₁)
    (hsN : s ∈ Subgroup.normalizer (oTwoUpper H : Set G)) :
    ∀ x ∈ imageOTwoQuot (oTwoUpper H) (oTwoUpper H₂), actHom (oTwoUpper H) ⟨s, hsN⟩ x = x := by
  intro x hx
  obtain ⟨k, hkK, hk, rfl⟩ := mem_imageOTwoQuot_iff.mp hx
  rw [actHom_mk, QuotientGroup.eq, mem_pCore_iff_coe]
  have hconj : s * k * s⁻¹ ∈ oTwoUpper H := (Subgroup.mem_normalizer_iff.mp hsN k).mp hkK
  show (s * k * s⁻¹)⁻¹ * k ∈ pCoreOf 2 (oTwoUpper H)
  refine (mem_pCoreOf_oTwoUpper_iff H).mpr
    ⟨(oTwoUpper H).mul_mem ((oTwoUpper H).inv_mem hconj) hkK, ?_⟩
  have e : (s * k * s⁻¹)⁻¹ * k = s * k⁻¹ * s⁻¹ * k⁻¹⁻¹ := by group
  rw [e]
  exact h.comm (Subgroup.commutator_mem_commutator hs (H₂.inv_mem (oTwoUpper_le H₂ hk)))

theorem actHom_inv_V₁ [NeZero p] (hp : Odd p) (h : IsDecP T M H p H₀ H₁ H₂ t) {s : G} (hs : s ∈ H₁)
    (hss : s * s ∈ pCoreOf 2 H) (hsQ : s ∉ pCoreOf 2 H)
    (hsN : s ∈ Subgroup.normalizer (oTwoUpper H : Set G)) :
    ∀ x ∈ imageOTwoQuot (oTwoUpper H) (oTwoUpper H₁),
      actHom (oTwoUpper H) ⟨s, hsN⟩ x = x⁻¹ := by
  intro x hx
  obtain ⟨k, hkK, hk, rfl⟩ := mem_imageOTwoQuot_iff.mp hx
  rw [actHom_mk, ← QuotientGroup.mk_inv, QuotientGroup.eq, mem_pCore_iff_coe]
  have hconj : s * k * s⁻¹ ∈ oTwoUpper H := (Subgroup.mem_normalizer_iff.mp hsN k).mp hkK
  show (s * k * s⁻¹)⁻¹ * k⁻¹ ∈ pCoreOf 2 (oTwoUpper H)
  refine (mem_pCoreOf_oTwoUpper_iff H).mpr
    ⟨(oTwoUpper H).mul_mem ((oTwoUpper H).inv_mem hconj) ((oTwoUpper H).inv_mem hkK), ?_⟩
  have e : (s * k * s⁻¹)⁻¹ * k⁻¹ = s * k⁻¹ * s⁻¹ * k⁻¹ := by group
  rw [e]
  exact reflection_conj_mem hp h hs hss hsQ ((oTwoUpper H₁).inv_mem hk)

theorem conjSub_oTwoUpper_H₁ (h : IsDecP T M H p H₀ H₁ H₂ t) :
    conjSub t (oTwoUpper H₁) = oTwoUpper H₂ := by
  rw [← oTwoUpper_conjSub_P, ← h.conj]

theorem conjSub_oTwoUpper_H₂ (h : IsDecP T M H p H₀ H₁ H₂ t) :
    conjSub t (oTwoUpper H₂) = oTwoUpper H₁ := by
  have ht2 : t ∉ Subgroup.normalizer (H₂ : Set G) := by
    intro hmem
    apply h.t_not
    have : t ∈ T ⊓ Subgroup.normalizer (H₁ : Set G) := by
      rw [← h.inf_normalizer_swap_eq]
      exact ⟨h.t_mem, hmem⟩
    exact this.2
  rw [← oTwoUpper_conjSub_P, h.swap.conjSub_eq_of_not_mem h.t_mem ht2]

theorem map_V₁ (h : IsDecP T M H p H₀ H₁ H₂ t)
    (htN : t ∈ Subgroup.normalizer (oTwoUpper H : Set G)) :
    (imageOTwoQuot (oTwoUpper H) (oTwoUpper H₁)).map
        (actHom (oTwoUpper H) ⟨t, htN⟩).toMonoidHom =
      imageOTwoQuot (oTwoUpper H) (oTwoUpper H₂) := by
  rw [map_actHom_imageOTwoQuot _ htN (oTwoUpper_mono (h.le₁.trans h.le)), conjSub_oTwoUpper_H₁ h]

theorem map_V₂ (h : IsDecP T M H p H₀ H₁ H₂ t)
    (htN : t ∈ Subgroup.normalizer (oTwoUpper H : Set G)) :
    (imageOTwoQuot (oTwoUpper H) (oTwoUpper H₂)).map
        (actHom (oTwoUpper H) ⟨t, htN⟩).toMonoidHom =
      imageOTwoQuot (oTwoUpper H) (oTwoUpper H₁) := by
  rw [map_actHom_imageOTwoQuot _ htN (oTwoUpper_mono (h.le₂.trans h.le)), conjSub_oTwoUpper_H₂ h]

end Elements

end SBc16

end CFSG.Quasithin
