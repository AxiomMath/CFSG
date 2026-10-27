module

public import CFSG.RankThree.OrthogonalInvolutions.Dickson
public import CFSG.ClassicalGroups.Orthogonal.Basic

public section

namespace CFSG.RankThree.PartOne.KCOrthogonal

open Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions CFSG.ClassicalGroups.Orthogonal

section Dickson

variable {K : Type*} [Field K] {W : Type*} [AddCommGroup W] [Module K W] [FiniteDimensional K W]
  {Q : QuadraticForm K W}

theorem dicksonHom_sq (hQ : Q.polarBilin.Nondegenerate)
    (g : TauCeti.QuadraticMap.orthogonalGroup Q) : dicksonHom Q hQ g ^ 2 = 1 := by
  have : ∀ a : Multiplicative (ZMod 2), a ^ 2 = 1 := by decide
  exact this _

theorem dicksonHom_eq_one_of_pow_eq_one (hQ : Q.polarBilin.Nondegenerate)
    {g : TauCeti.QuadraticMap.orthogonalGroup Q} {n : ℕ} (hn : Odd n) (hg : g ^ n = 1) :
    dicksonHom Q hQ g = 1 := by
  obtain ⟨k, rfl⟩ := hn
  have h1 : dicksonHom Q hQ g ^ (2 * k + 1) = 1 := by rw [← map_pow, hg, map_one]
  rwa [pow_succ, pow_mul, dicksonHom_sq, one_pow, one_mul] at h1

theorem even_finrank_commSpace_of_dicksonHom_eq_one (hQ : Q.polarBilin.Nondegenerate)
    {g : TauCeti.QuadraticMap.orthogonalGroup Q} (hg : dicksonHom Q hQ g = 1) :
    Even (finrank K (commSpace (g : W ≃ₗ[K] W))) := by
  rw [dicksonHom_apply, ← ofAdd_zero, Multiplicative.ofAdd.injective.eq_iff] at hg
  exact ZMod.natCast_eq_zero_iff_even.mp hg

theorem eq_one_of_finrank_le_one (hQ : Q.polarBilin.Nondegenerate) (hW : finrank K W ≤ 1)
    {g : TauCeti.QuadraticMap.orthogonalGroup Q} {n : ℕ} (hn : Odd n) (hg : g ^ n = 1) :
    (g : W ≃ₗ[K] W) = 1 := by
  have hev := even_finrank_commSpace_of_dicksonHom_eq_one hQ
    (dicksonHom_eq_one_of_pow_eq_one hQ hn hg)
  have hle : finrank K (commSpace (g : W ≃ₗ[K] W)) ≤ 1 :=
    (Submodule.finrank_le _).trans hW
  have h0 : finrank K (commSpace (g : W ≃ₗ[K] W)) = 0 := by
    obtain ⟨m, hm⟩ := hev
    omega
  have hbot : commSpace (g : W ≃ₗ[K] W) = ⊥ := Submodule.finrank_eq_zero.mp h0
  ext v
  have hv : (g : W ≃ₗ[K] W) v - v ∈ commSpace (g : W ≃ₗ[K] W) := sub_mem_commSpace _ v
  rw [hbot, Submodule.mem_bot, sub_eq_zero] at hv
  rw [hv, LinearEquiv.coe_one, id]

end Dickson

section Transvection

variable {K : Type*} [Field K] {W : Type*} [AddCommGroup W] [Module K W] [FiniteDimensional K W]
  {Q : QuadraticForm K W}

theorem mul_self_eq_one_of_finrank_commSpace_eq_one (hQ : Q.polarBilin.Nondegenerate)
    {t : W ≃ₗ[K] W} (ht : t ∈ TauCeti.QuadraticMap.orthogonalGroup Q)
    (h1 : finrank K (commSpace t) = 1) : t * t = 1 := by
  obtain ⟨v₀, hv₀⟩ : ∃ v₀, t v₀ ≠ v₀ := by
    by_contra! h
    have hbot : commSpace t = ⊥ := by
      rw [eq_bot_iff]
      intro y hy
      obtain ⟨v, rfl⟩ := mem_commSpace.mp hy
      simp [h v]
    rw [hbot, finrank_bot] at h1
    exact zero_ne_one h1
  set c := t v₀ - v₀ with hc
  have hc0 : c ≠ 0 := sub_ne_zero.mpr hv₀
  have hspan : commSpace t = K ∙ c := by
    symm
    apply Submodule.eq_of_le_of_finrank_eq
    · rw [Submodule.span_singleton_le_iff_mem]
      exact sub_mem_commSpace t v₀
    · rw [finrank_span_singleton hc0, h1]
  have hmul : ∀ v, ∃ s : K, t v - v = s • c := fun v => by
    have : t v - v ∈ K ∙ c := hspan ▸ sub_mem_commSpace t v
    obtain ⟨s, hs⟩ := Submodule.mem_span_singleton.mp this
    exact ⟨s, hs.symm⟩
  have hQt : ∀ v, Q (t v) = Q v := TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mp ht
  have hpol : ∀ u v, polar Q (t u) (t v) = polar Q u v :=
    TauCeti.QuadraticMap.polar_apply_of_mem_orthogonalGroup ht
  have hfix : ∀ v, t v = v → polar Q v c = 0 := by
    intro v hv
    have h2 : polar Q v (t v₀) = polar Q v v₀ := by
      have := hpol v v₀
      rwa [hv] at this
    rw [hc, QuadraticMap.polar_sub_right, h2, sub_self]
  have hexp : ∀ v (s : K), t v - v = s • c →
      s * (s * Q c + polar Q v c) = 0 := by
    intro v s hs
    have htv : t v = v + s • c := by rw [← hs]; abel
    have h2 := hQt v
    rw [htv, map_add_eq, QuadraticMap.map_smul, QuadraticMap.polar_smul_right, smul_eq_mul,
      smul_eq_mul] at h2
    linear_combination h2
  have hQc : Q c ≠ 0 := by
    intro hQc0
    have hall : ∀ v, polar Q v c = 0 := by
      intro v
      obtain ⟨s, hs⟩ := hmul v
      by_cases hs0 : s = 0
      · rw [hs0, zero_smul, sub_eq_zero] at hs
        exact hfix v hs
      · have := hexp v s hs
        rw [hQc0, mul_zero, zero_add] at this
        exact (mul_eq_zero.mp this).resolve_left hs0
    exact hc0 (hQ.1 c fun w => by rw [polarBilin_apply_apply, polar_comm]; exact hall w)
  obtain ⟨s₁, hs₁⟩ := hmul c
  have htc : t c = (1 + s₁) • c := by
    rw [add_smul, one_smul, ← hs₁]; abel
  have hμ : 1 + s₁ = -1 := by
    have hE3 : Q c + polar Q v₀ c = 0 := by
      have := hexp v₀ 1 (by rw [one_smul])
      rw [one_mul, one_mul] at this
      exact this
    have hE1 := hpol v₀ c
    have htv₀ : t v₀ = v₀ + c := by rw [hc]; abel
    rw [htv₀, htc, QuadraticMap.polar_add_left, QuadraticMap.polar_smul_right,
      QuadraticMap.polar_smul_right, polar_self_eq_two_mul, smul_eq_mul, smul_eq_mul] at hE1
    have hpv : polar Q v₀ c = -Q c := by linear_combination hE3
    rw [hpv] at hE1
    have h3 : Q c * (1 + s₁ + 1) = 0 := by linear_combination hE1
    have := (mul_eq_zero.mp h3).resolve_left hQc
    linear_combination this
  ext v
  obtain ⟨s, hs⟩ := hmul v
  have htv : t v = v + s • c := by rw [← hs]; abel
  show t (t v) = v
  calc t (t v) = t (v + s • c) := congrArg t htv
    _ = t v + s • t c := by rw [map_add, map_smul]
    _ = v := by
      rw [htv, htc, hμ]
      module

end Transvection

section Binary

variable {K : Type*} [Field K] {W : Type*} [AddCommGroup W] [Module K W] [FiniteDimensional K W]
  {Q : QuadraticForm K W}

theorem commute_of_dicksonHom_eq_one (hQ : Q.polarBilin.Nondegenerate) (h2 : finrank K W = 2)
    {g k : W ≃ₗ[K] W} (hg : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q)
    (hk : k ∈ TauCeti.QuadraticMap.orthogonalGroup Q)
    (hgδ : dicksonHom Q hQ ⟨g, hg⟩ = 1) (hkδ : dicksonHom Q hQ ⟨k, hk⟩ = 1) :
    g * k = k * g := by
  have : Nontrivial W := Module.nontrivial_of_finrank_pos (R := K) (by omega)
  obtain ⟨a, ha⟩ := exists_map_ne_zero hQ
  let _ : Invertible (Q a) := invertibleOfNonzero ha
  set s := TauCeti.QuadraticMap.reflection Q a with hs
  have hsO : s ∈ TauCeti.QuadraticMap.orthogonalGroup Q :=
    TauCeti.QuadraticMap.reflection_mem_orthogonalGroup Q a
  have hs1 : finrank K (commSpace s) = 1 := finrank_commSpace_reflection hQ a
  have hss : s * s = 1 := mul_self_eq_one_of_finrank_commSpace_eq_one hQ hsO hs1
  have hδs : dicksonHom Q hQ ⟨s, hsO⟩ = Multiplicative.ofAdd (1 : ZMod 2) := by
    rw [dicksonHom_apply]
    simp only [hs1, Nat.cast_one]
  have key : ∀ (u : W ≃ₗ[K] W) (hu : u ∈ TauCeti.QuadraticMap.orthogonalGroup Q),
      dicksonHom Q hQ ⟨u, hu⟩ = 1 → s * u * s = u⁻¹ := by
    intro u hu hδu
    have hus : u * s ∈ TauCeti.QuadraticMap.orthogonalGroup Q := mul_mem hu hsO
    have hδus : dicksonHom Q hQ ⟨u * s, hus⟩ = Multiplicative.ofAdd (1 : ZMod 2) := by
      have : (⟨u * s, hus⟩ : TauCeti.QuadraticMap.orthogonalGroup Q) = ⟨u, hu⟩ * ⟨s, hsO⟩ := rfl
      rw [this, map_mul, hδu, hδs, one_mul]
    have hodd : (finrank K (commSpace (u * s)) : ZMod 2) = 1 := by
      rw [dicksonHom_apply] at hδus
      exact Multiplicative.ofAdd.injective hδus
    have hle : finrank K (commSpace (u * s)) ≤ 2 := (Submodule.finrank_le _).trans h2.le
    have h1' : finrank K (commSpace (u * s)) = 1 := by
      generalize finrank K (commSpace (u * s)) = n at hodd hle
      interval_cases n
      · exact absurd hodd (by decide)
      · rfl
      · exact absurd hodd (by decide)
    have hsq := mul_self_eq_one_of_finrank_commSpace_eq_one hQ hus h1'
    apply eq_inv_of_mul_eq_one_right
    calc u * (s * u * s) = u * s * (u * s) := by simp only [mul_assoc]
      _ = 1 := hsq
  have hgk : g * k ∈ TauCeti.QuadraticMap.orthogonalGroup Q := mul_mem hg hk
  have hδgk : dicksonHom Q hQ ⟨g * k, hgk⟩ = 1 := by
    have : (⟨g * k, hgk⟩ : TauCeti.QuadraticMap.orthogonalGroup Q) = ⟨g, hg⟩ * ⟨k, hk⟩ := rfl
    rw [this, map_mul, hgδ, hkδ, one_mul]
  have h3 : (g * k)⁻¹ = (s * g * s) * (s * k * s) := by
    calc (g * k)⁻¹ = s * (g * k) * s := (key _ hgk hδgk).symm
      _ = s * g * (s * s) * k * s := by rw [hss]; simp only [mul_one, mul_assoc]
      _ = (s * g * s) * (s * k * s) := by simp only [mul_assoc]
  rw [key g hg hgδ, key k hk hkδ, mul_inv_rev] at h3
  have h4 : k⁻¹ * g⁻¹ = g⁻¹ * k⁻¹ := h3
  have h5 := congrArg (fun z => z⁻¹) h4
  simpa [mul_inv_rev] using h5

end Binary

end CFSG.RankThree.PartOne.KCOrthogonal
