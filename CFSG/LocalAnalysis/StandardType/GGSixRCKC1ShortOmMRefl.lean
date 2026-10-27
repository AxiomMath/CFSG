module

public import CFSG.ClassicalGroups.Orthogonal.RootGroupStabilizerFour
public import CFSG.ClassicalGroups.Orthogonal.RootGroupChar
public import CFSG.ClassicalGroups.Orthogonal.Hyperbolic
public import CFSG.ClassicalGroups.Orthogonal.RootGroupNormalizer
public import CFSG.LieType.BorelTits.CompleteFlag

public section

namespace CFSG.StandardType.RCKC1

open Module QuadraticMap CFSG.ClassicalGroups.Orthogonal CFSG.RankThree.OrthogonalInvolutions

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}

theorem rckSOmMR_quad_span {e w : V} (he : Q e = 0) (hew : polar Q e w = 0) (a b : K) :
    Q (a • e + b • w) = b ^ 2 * Q w := by
  rw [QuadraticMap.map_add Q, map_smul_eq_sq, map_smul_eq_sq, polar_smul_left_eq,
    polar_smul_right_eq, he, hew]
  ring

private theorem rckSOmMR_linearIndependent {e w : V} (he : Q e = 0) (hew : polar Q e w = 0)
    (hw : Q w ≠ 0) (he0 : e ≠ 0) : LinearIndependent K ![e, w] := by
  rw [LinearIndependent.pair_iff]
  intro a b hab
  have hQ0 : Q (a • e + b • w) = 0 := by rw [hab, map_zero]
  rw [rckSOmMR_quad_span he hew] at hQ0
  have hb : b = 0 := by
    have hb2 : b ^ 2 * Q w = 0 := hQ0
    exact (pow_eq_zero_iff two_ne_zero).mp ((mul_eq_zero.mp hb2).resolve_right hw)
  subst hb
  simp only [zero_smul, add_zero] at hab
  exact ⟨(smul_eq_zero.mp hab).resolve_right he0, rfl⟩

private theorem rckSOmMR_dual [FiniteDimensional K V] (hQ : (polarBilin Q).Nondegenerate)
    {e w : V} (he : Q e = 0) (hew : polar Q e w = 0) (hw : Q w ≠ 0) (he0 : e ≠ 0) :
    ∃ g0 g1 : V, polar Q e g0 = 1 ∧ polar Q e g1 = 0 ∧ polar Q w g0 = 0 ∧ polar Q w g1 = 1 := by
  obtain ⟨g, hg⟩ := exists_dual_family hQ (t := ![e, w])
    (rckSOmMR_linearIndependent he hew hw he0)
  exact ⟨g 0, g 1, by simpa using hg 0 0, by simpa using hg 0 1, by simpa using hg 1 0,
    by simpa using hg 1 1⟩

theorem rckSOmMR_exists_of_orth [FiniteDimensional K V] (hQ : (polarBilin Q).Nondegenerate)
    {e w : V} (he : Q e = 0) (he0 : e ≠ 0) (hew : polar Q e w = 0) (hw : Q w ≠ 0) {d : V}
    (hd : ∀ x, polar Q x e = 0 → polar Q x w = 0 → polar Q x d = 0) :
    ∃ α l : K, d = α • e + l • w := by
  obtain ⟨g0, g1, hg00, hg01, hg10, hg11⟩ := rckSOmMR_dual hQ he hew hw he0
  have hg0e : polar Q g0 e = 1 := by rw [polar_comm]; exact hg00
  have hg0w : polar Q g0 w = 0 := by rw [polar_comm]; exact hg10
  have hg1e : polar Q g1 e = 0 := by rw [polar_comm]; exact hg01
  have hg1w : polar Q g1 w = 1 := by rw [polar_comm]; exact hg11
  refine ⟨polar Q g0 d, polar Q g1 d, ?_⟩
  have hproj : ∀ x, polar Q x d = polar Q x e * polar Q g0 d + polar Q x w * polar Q g1 d := by
    intro x
    have h1 := hd (x - polar Q x e • g0 - polar Q x w • g1) (by
      rw [polar_sub_left, polar_sub_left, polar_smul_left_eq, polar_smul_left_eq, hg0e, hg1e]
      ring) (by
      rw [polar_sub_left, polar_sub_left, polar_smul_left_eq, polar_smul_left_eq, hg0w, hg1w]
      ring)
    rw [polar_sub_left, polar_sub_left, polar_smul_left_eq, polar_smul_left_eq] at h1
    linear_combination h1
  have hz : d - (polar Q g0 d • e + polar Q g1 d • w) = 0 := by
    refine hQ.1 _ fun x => ?_
    rw [polarBilin_apply_apply, polar_comm, polar_sub_right, polar_add_right,
      polar_smul_right_eq, polar_smul_right_eq, hproj x]
    ring
  exact sub_eq_zero.mp hz

private theorem rckSOmMR_not_refl [CharP K 2] [FiniteDimensional K V]
    (hQ : (polarBilin Q).Nondegenerate) {e w : V} (he : Q e = 0) (he0 : e ≠ 0)
    (hew : polar Q e w = 0) (hw : Q w ≠ 0) {T : V ≃ₗ[K] V} (hTΩ : T ∈ omegaGroup Q hQ)
    (hTe : T e = e)
    (hrefl : ∀ x, polar Q x e = 0 →
      ∃ c : K, T x - x = ((Q w)⁻¹ * polar Q x w) • w + c • e) : False := by
  haveI : Invertible (Q w) := invertibleOfNonzero hw
  have hww : polar Q w w = 0 := polar_self_eq_zero Q w
  have hwe : polar Q w e = 0 := by rw [polar_comm]; exact hew
  have hrO : TauCeti.QuadraticMap.reflection Q w ∈ TauCeti.QuadraticMap.orthogonalGroup Q :=
    TauCeti.QuadraticMap.reflection_mem_orthogonalGroup Q w
  have hr_not : TauCeti.QuadraticMap.reflection Q w ∉ omegaGroup Q hQ := by
    intro h
    have h1 := (mem_omegaGroup.mp h).2
    rw [finrank_commSpace_reflection hQ w] at h1
    exact Nat.not_even_one h1
  have hT' : TauCeti.QuadraticMap.reflection Q w * T ∈ rootGroup Q e := by
    rw [mem_rootGroup_iff hQ he he0]
    refine ⟨mul_mem hrO (omegaGroup_le Q hQ hTΩ), ?_, ?_⟩
    · show TauCeti.QuadraticMap.reflection Q w (T e) = e
      rw [hTe, TauCeti.QuadraticMap.reflection_apply, hwe]
      simp
    · intro x hx
      obtain ⟨c, hc⟩ := hrefl x hx
      refine ⟨c, ?_⟩
      have hTx : T x = x + (((Q w)⁻¹ * polar Q x w) • w + c • e) := by rw [← hc]; abel
      have hpol : polar Q w (T x) = polar Q x w := by
        rw [hTx, polar_add_right, polar_add_right, polar_smul_right_eq, polar_smul_right_eq, hww,
          hwe, polar_comm Q w x]
        ring
      show TauCeti.QuadraticMap.reflection Q w (T x) - x = c • e
      rw [TauCeti.QuadraticMap.reflection_apply, hpol, invOf_eq_inv, hTx]
      module
  have hrΩ : TauCeti.QuadraticMap.reflection Q w ∈ omegaGroup Q hQ := by
    have h1 : TauCeti.QuadraticMap.reflection Q w * T ∈ omegaGroup Q hQ := by
      obtain ⟨w', hw', hw'eq⟩ := mem_rootGroup.mp hT'
      rw [← hw'eq]
      exact elementaryGroup_le_omegaGroup hQ (eichler_mem_elementaryGroup Q e w')
    have h2 : TauCeti.QuadraticMap.reflection Q w =
        (TauCeti.QuadraticMap.reflection Q w * T) * T⁻¹ :=
      (mul_inv_cancel_right (TauCeti.QuadraticMap.reflection Q w) T).symm
    rw [h2]
    exact mul_mem h1 (inv_mem hTΩ)
  exact hr_not hrΩ

theorem rckSOmMR_mem_rootGroup [CharP K 2] [FiniteDimensional K V]
    (hQ : (polarBilin Q).Nondegenerate) {e w : V} (he : Q e = 0) (he0 : e ≠ 0)
    (hew : polar Q e w = 0) (hw : Q w ≠ 0) {T : V ≃ₗ[K] V} (hTΩ : T ∈ omegaGroup Q hQ)
    (hTe : T e = e) (hcomm : ∀ x, T (eichler Q e w x) = eichler Q e w (T x))
    (hP : ∀ x, polar Q x e = 0 → polar Q x w = 0 → ∃ c : K, T x - x = c • e) :
    T ∈ rootGroup Q e := by
  have hTO : T ∈ TauCeti.QuadraticMap.orthogonalGroup Q := omegaGroup_le Q hQ hTΩ
  obtain ⟨g0, g1, hg00, hg01, hg10, hg11⟩ := rckSOmMR_dual hQ he hew hw he0
  have hwe : polar Q w e = 0 := by rw [polar_comm]; exact hew
  have hww : polar Q w w = 0 := polar_self_eq_zero Q w
  have hu0e : polar Q g1 e = 0 := by rw [polar_comm]; exact hg01
  have hu0w : polar Q g1 w = 1 := by rw [polar_comm]; exact hg11
  have hg0e : polar Q g0 e = 1 := by rw [polar_comm]; exact hg00
  have hg0w : polar Q g0 w = 0 := by rw [polar_comm]; exact hg10
  have hTu0e : polar Q (T g1) e = 0 := by
    have h := polar_map_of_mem hTO g1 e
    rw [hTe] at h
    rw [h]
    exact hu0e
  have hEx : ∀ x, eichler Q e w x =
      x + polar Q x e • w - (polar Q x w + Q w * polar Q x e) • e :=
    fun x => eichler_apply he hew x
  have hTu0w : polar Q (T g1) w = 1 := by
    have h := hcomm g1
    rw [hEx g1, hEx (T g1), hu0e, hu0w, hTu0e] at h
    simp only [zero_smul, add_zero, mul_zero, map_sub, map_add, one_smul, hTe] at h
    have h2 : e = polar Q (T g1) w • e := sub_right_inj.mp h
    have h3 : polar Q (T g1) w • e = (1 : K) • e := by rw [one_smul]; exact h2.symm
    exact smul_left_injective K he0 h3
  obtain ⟨d₀, hd₀⟩ : ∃ d₀ : V, d₀ = T g1 - g1 := ⟨_, rfl⟩
  have hd0e : polar Q d₀ e = 0 := by rw [hd₀, polar_sub_left, hTu0e, hu0e, sub_zero]
  have hd0w : polar Q d₀ w = 0 := by rw [hd₀, polar_sub_left, hTu0w, hu0w, sub_self]
  have hQd : ∀ x₁, polar Q x₁ e = 0 → polar Q x₁ w = 0 →
      Q d₀ + (polar Q x₁ d₀ + polar Q g1 d₀) = 0 := by
    intro x₁ hx1e hx1w
    obtain ⟨a, ha⟩ := hP x₁ hx1e hx1w
    have hTx1 : T x₁ = x₁ + a • e := by rw [← ha]; abel
    have hT1 : T (x₁ + g1) = (x₁ + g1 + d₀) + a • e := by
      rw [map_add, hTx1, hd₀]
      abel
    have hQ1 : Q (T (x₁ + g1)) = Q (x₁ + g1) := map_of_mem hTO _
    rw [hT1] at hQ1
    have hbe : polar Q (x₁ + g1 + d₀) e = 0 := by
      rw [polar_add_left, polar_add_left, hx1e, hu0e, hd0e]
      simp
    rw [QuadraticMap.map_add Q (x₁ + g1 + d₀) (a • e), map_smul_eq_sq, he, polar_smul_right_eq,
      hbe, QuadraticMap.map_add Q (x₁ + g1) d₀, polar_add_left] at hQ1
    linear_combination hQ1
  have hQd0 : Q d₀ + polar Q g1 d₀ = 0 := by
    have h := hQd 0 (by rw [polar_zero_left]) (by rw [polar_zero_left])
    rw [polar_zero_left, zero_add] at h
    exact h
  have hkey : ∀ x₁, polar Q x₁ e = 0 → polar Q x₁ w = 0 → polar Q x₁ d₀ = 0 := by
    intro x₁ hx1e hx1w
    have h := hQd x₁ hx1e hx1w
    linear_combination h - hQd0
  obtain ⟨α, l, hd⟩ := rckSOmMR_exists_of_orth hQ he he0 hew hw hkey
  have hl : polar Q g1 d₀ = l := by
    rw [hd, polar_add_right, polar_smul_right_eq, polar_smul_right_eq, hu0e, hu0w]
    ring
  have hl_eq : l * (l * Q w + 1) = 0 := by
    have h1 : Q d₀ = l ^ 2 * Q w := by rw [hd, rckSOmMR_quad_span he hew]
    rw [hl, h1] at hQd0
    linear_combination hQd0
  have hdec : ∀ x, polar Q x e = 0 →
      ∃ a : K, T x - x = a • e + polar Q x w • d₀ := by
    intro x hx
    have hx1e : polar Q (x - polar Q x w • g1) e = 0 := by
      rw [polar_sub_left, polar_smul_left_eq, hu0e, hx]
      ring
    have hx1w : polar Q (x - polar Q x w • g1) w = 0 := by
      rw [polar_sub_left, polar_smul_left_eq, hu0w]
      ring
    obtain ⟨a, ha⟩ := hP _ hx1e hx1w
    refine ⟨a, ?_⟩
    have hTx : T x = T (x - polar Q x w • g1) + polar Q x w • T g1 := by
      have h := T.map_add (x - polar Q x w • g1) (polar Q x w • g1)
      rw [sub_add_cancel, T.map_smul] at h
      exact h
    have hTx1 : T (x - polar Q x w • g1) = (x - polar Q x w • g1) + a • e := by
      rw [← ha]; abel
    rw [hTx, hTx1, hd₀]
    module
  by_cases hl0 : l = 0
  · rw [mem_rootGroup_iff hQ he he0]
    refine ⟨hTO, hTe, fun x hx => ?_⟩
    obtain ⟨a, ha⟩ := hdec x hx
    refine ⟨a + polar Q x w * α, ?_⟩
    rw [ha, hd, hl0]
    module
  · exfalso
    have hlQ : l * Q w = 1 := by
      have h := (mul_eq_zero.mp hl_eq).resolve_left hl0
      have h' : l * Q w = -1 := eq_neg_of_add_eq_zero_left h
      rw [h', CharTwo.neg_eq]
    have hl_inv : l = (Q w)⁻¹ := eq_inv_of_mul_eq_one_left hlQ
    refine rckSOmMR_not_refl hQ he he0 hew hw hTΩ hTe fun x hx => ?_
    obtain ⟨a, ha⟩ := hdec x hx
    refine ⟨a + polar Q x w * α, ?_⟩
    rw [ha, hd, ← hl_inv]
    module

end CFSG.StandardType.RCKC1
