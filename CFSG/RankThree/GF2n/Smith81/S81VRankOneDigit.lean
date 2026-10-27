module

public import CFSG.RankThree.GF2n.Smith81.S81VRankOneMon

public section

namespace CFSG.RankThree.GF2n.Smith81.S81V

open Module

namespace RankOneData

variable {K : Type} [Field K] [Fintype K] [CharP K 2] {V : Type} [AddCommGroup V] [Module K V]
  {D : RankOneData K V} {v₀ : V} {k : ℕ} {f : ℕ}

private theorem X_invol_apply (t : K) (w : V) : D.X t (D.X t w) = w := by
  have h := congrArg (fun F : V ≃ₗ[K] V => F w) (D.X_mul_self t)
  exact h

private theorem Exp.X_eq_sum_apply (X : D.Exp f) (t : K) (u : V) :
    D.X t u = ∑ B : Finset (Fin f), t ^ bitSum B • X.E B u := by
  have h := congrArg (fun F : V →ₗ[K] V => F u) (X.hE t)
  simpa using h

theorem Exp.beta_adjoint (X : D.Exp f) {β : V →ₗ[K] V →ₗ[K] K}
    (hβρ : ∀ n u w, β (D.ρ n u) (D.ρ n w) = β u w) (B : Finset (Fin f)) (u w : V) :
    β (X.E B u) w = β u (X.E B w) := by
  have hX : ∀ t : K, β (D.X t u) w = β u (D.X t w) := by
    intro t
    have h1 : β (D.X t u) (D.X t (D.X t w)) = β u (D.X t w) := hβρ (t • D.n₁) u (D.X t w)
    rwa [X_invol_apply] at h1
  have hsum : ∀ t : K, ∑ B' : Finset (Fin f),
      t ^ bitSum B' * (β (X.E B' u) w - β u (X.E B' w)) = 0 := by
    intro t
    have h1 := hX t
    rw [X.X_eq_sum_apply t u, X.X_eq_sum_apply t w] at h1
    simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul] at h1
    simp only [mul_sub, Finset.sum_sub_distrib]
    exact sub_eq_zero.2 h1
  exact sub_eq_zero.1 (coeff_eq_zero_of_sum_pow_eq_zero X.hf
    (fun B' => β (X.E B' u) w - β u (X.E B' w)) hsum B)

theorem Exp.X_digit (X : D.Exp f) {B' : Finset (Fin f)}
    (hB' : ∀ B, X.E B (D.s v₀) ≠ 0 ↔ B ⊆ B') {r : Fin f} (hr : r ∈ B') (t : K) :
    D.X t (X.E (B'.erase r) (D.s v₀)) =
      X.E (B'.erase r) (D.s v₀) + (t ^ (2 ^ (r : ℕ))) • X.E B' (D.s v₀) := by
  have hEz : ∀ B : Finset (Fin f), X.E B (X.E (B'.erase r) (D.s v₀)) =
      if Disjoint B (B'.erase r) then X.E (B ∪ B'.erase r) (D.s v₀) else 0 := by
    intro B
    have h1 := congrArg (fun F : V →ₗ[K] V => F (D.s v₀)) (X.hprod B (B'.erase r))
    simp only [Module.End.mul_apply] at h1
    rw [h1]
    split_ifs <;> simp
  have hXz : D.X t (X.E (B'.erase r) (D.s v₀)) = ∑ B : Finset (Fin f),
      t ^ bitSum B • (if Disjoint B (B'.erase r) then X.E (B ∪ B'.erase r) (D.s v₀) else 0) := by
    rw [X.X_eq_sum_apply t]
    exact Finset.sum_congr rfl fun B _ => by rw [hEz B]
  have hsub_lemma : ∀ B : Finset (Fin f), Disjoint B (B'.erase r) → B ∪ B'.erase r ⊆ B' →
      B = ∅ ∨ B = {r} := by
    intro B hBC hBsub
    rw [← Finset.subset_singleton_iff]
    intro x hx
    rw [Finset.mem_singleton]
    by_contra hxr
    have hxB' : x ∈ B' := hBsub (Finset.mem_union_left _ hx)
    exact Finset.disjoint_left.1 hBC hx (Finset.mem_erase.2 ⟨hxr, hxB'⟩)
  have hterm : ∀ B ∈ (Finset.univ : Finset (Finset (Fin f))),
      B ∉ ({∅, {r}} : Finset (Finset (Fin f))) →
      t ^ bitSum B • (if Disjoint B (B'.erase r) then X.E (B ∪ B'.erase r) (D.s v₀) else 0) = 0 := by
    intro B _ hB
    split_ifs with hBC
    · have hz : X.E (B ∪ B'.erase r) (D.s v₀) = 0 := by
        by_contra hne
        have hsub' : B ∪ B'.erase r ⊆ B' := (hB' (B ∪ B'.erase r)).1 hne
        rcases hsub_lemma B hBC hsub' with h0 | h0
        · exact hB (by simp [h0])
        · exact hB (by simp [h0])
      rw [hz, smul_zero]
    · rw [smul_zero]
  have hne : (∅ : Finset (Fin f)) ≠ {r} := (Finset.singleton_ne_empty r).symm
  have hdisj : Disjoint ({r} : Finset (Fin f)) (B'.erase r) := by simp
  have hU : ({r} : Finset (Fin f)) ∪ B'.erase r = B' := by
    rw [← Finset.insert_eq, Finset.insert_erase hr]
  have hb0 : bitSum (∅ : Finset (Fin f)) = 0 := by simp [bitSum]
  have hb1 : bitSum ({r} : Finset (Fin f)) = 2 ^ (r : ℕ) := by simp [bitSum]
  have h0 : t ^ bitSum (∅ : Finset (Fin f)) •
      (if Disjoint (∅ : Finset (Fin f)) (B'.erase r) then
        X.E ((∅ : Finset (Fin f)) ∪ B'.erase r) (D.s v₀) else 0) = X.E (B'.erase r) (D.s v₀) := by
    rw [hb0, pow_zero, one_smul, if_pos (Finset.disjoint_empty_left (B'.erase r)),
      Finset.empty_union]
  have h1 : t ^ bitSum ({r} : Finset (Fin f)) •
      (if Disjoint ({r} : Finset (Fin f)) (B'.erase r) then
        X.E ({r} ∪ B'.erase r) (D.s v₀) else 0) = (t ^ (2 ^ (r : ℕ))) • X.E B' (D.s v₀) := by
    rw [hb1, if_pos hdisj, hU]
  rw [hXz, ← Finset.sum_subset (Finset.subset_univ ({∅, {r}} : Finset (Finset (Fin f)))) hterm,
    Finset.sum_pair hne, h0, h1]

theorem Exp.rho_digit [FiniteDimensional K V] (X : D.Exp f) (h : D.Setup v₀ k) {B' : Finset (Fin f)}
    (hB' : ∀ B, X.E B (D.s v₀) ≠ 0 ↔ B ⊆ B') {r : Fin f} (hr : r ∈ B') (n : D.N) :
    D.ρ n (X.E (B'.erase r) (D.s v₀)) - X.E (B'.erase r) (D.s v₀) =
      ((D.τ n) ^ (2 ^ (r : ℕ))) • X.E B' (D.s v₀) := by
  have hw : X.E (B'.erase r) (D.s v₀) ∈ D.S v₀ := D.E_apply_mem_S X.hspan (B'.erase r)
  rw [D.rho_eq_X_on_S h.fix1 h.mem h.ne0 hw n, X.X_digit hB' hr (D.τ n)]
  abel

theorem Exp.beta_digit [FiniteDimensional K V] (X : D.Exp f) (h : D.Setup v₀ k)
    {β : V →ₗ[K] V →ₗ[K] K} (hβρ : ∀ n u w, β (D.ρ n u) (D.ρ n w) = β u w) {B' : Finset (Fin f)}
    (hB' : ∀ B, X.E B (D.s v₀) ≠ 0 ↔ B ⊆ B') (hv' : X.E B' (D.s v₀) ∈ D.fix)
    (hv'0 : X.E B' (D.s v₀) ≠ 0) {r : Fin f} (hr : r ∈ B') (h2 : 2 ≤ B'.card) :
    ∀ v ∈ D.fix, β v (X.E (B'.erase r) (D.s v₀)) = 0 := by
  intro v hv
  have hne : (B'.erase r).Nonempty := by
    rw [← Finset.card_pos, Finset.card_erase_of_mem hr]
    omega
  obtain ⟨x, hx⟩ := hne
  have hdisj : ¬ Disjoint B' (B'.erase r) := fun hd =>
    Finset.disjoint_left.1 hd (Finset.mem_of_mem_erase hx) hx
  have hprodz : X.E B' (X.E (B'.erase r) (D.s v₀)) = 0 := by
    have h1 := congrArg (fun F : V →ₗ[K] V => F (D.s v₀)) (X.hprod B' (B'.erase r))
    simp only [Module.End.mul_apply] at h1
    rw [h1, if_neg hdisj, LinearMap.zero_apply]
  have hzero : β (X.E B' (D.s v₀)) (X.E (B'.erase r) (D.s v₀)) = 0 := by
    rw [X.beta_adjoint hβρ B' (D.s v₀) (X.E (B'.erase r) (D.s v₀)), hprodz, map_zero]
  have hne0 : (⟨X.E B' (D.s v₀), hv'⟩ : D.fix) ≠ 0 := by
    intro h0
    have h1 := congrArg Subtype.val h0
    exact hv'0 h1
  obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' _ hne0).1 h.fix1 ⟨v, hv⟩
  have hcv : c • X.E B' (D.s v₀) = v := by
    have h1 := congrArg Subtype.val hc
    exact h1
  rw [← hcv, map_smul, LinearMap.smul_apply, hzero, smul_zero]

theorem Exp.digit_mem_V1 [FiniteDimensional K V] (X : D.Exp f) (h : D.Setup v₀ k)
    {β : V →ₗ[K] V →ₗ[K] K} (hβρ : ∀ n u w, β (D.ρ n u) (D.ρ n w) = β u w) {B' : Finset (Fin f)}
    (hB' : ∀ B, X.E B (D.s v₀) ≠ 0 ↔ B ⊆ B') (hv' : X.E B' (D.s v₀) ∈ D.fix)
    (hv'0 : X.E B' (D.s v₀) ≠ 0) {r : Fin f} (hr : r ∈ B') (h2 : 2 ≤ B'.card) :
    X.E (B'.erase r) (D.s v₀) ∈ D.V1 β := by
  refine ⟨X.beta_digit h hβρ hB' hv' hv'0 hr h2, fun n => ?_⟩
  rw [X.rho_digit h hB' hr n]
  exact D.fix.smul_mem _ hv'

theorem V1_stable {β : V →ₗ[K] V →ₗ[K] K} (hβa : ∀ g u w, β (D.a g u) (D.a g w) = β u w) (g : D.Pg)
    {w : V} (hw : w ∈ D.V1 β) : D.a g w ∈ D.V1 β := by
  obtain ⟨hw1, hw2⟩ := hw
  refine ⟨fun v hv => ?_, fun n => ?_⟩
  ·
    have hinv : D.a g * D.a g⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel, map_one]
    have hv_eq : D.a g (D.a g⁻¹ v) = v := by
      have h1 := congrArg (fun F : V ≃ₗ[K] V => F v) hinv
      exact h1
    have h2 := hβa g (D.a g⁻¹ v) w
    rw [hv_eq] at h2
    rw [h2]
    exact hw1 _ (D.a_mem_fix g⁻¹ hv)
  ·
    have hAd1 : D.Ad g * D.Ad g⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel, map_one]
    have hAd : D.Ad g (D.Ad g⁻¹ n) = n := by
      have h1 := congrArg (fun F : D.N ≃ₗ[K] D.N => F n) hAd1
      exact h1
    have hρ := D.Ad_spec g (D.Ad g⁻¹ n)
    rw [hAd] at hρ
    have key : D.ρ n * D.a g = D.a g * D.ρ (D.Ad g⁻¹ n) := by
      rw [hρ]
      simp [mul_assoc]
    have h1 : D.ρ n (D.a g w) = D.a g (D.ρ (D.Ad g⁻¹ n) w) := by
      have h2 := congrArg (fun F : V ≃ₗ[K] V => F w) key
      simpa only [LinearEquiv.mul_apply] using h2
    have h2 : D.ρ n (D.a g w) - D.a g w = D.a g (D.ρ (D.Ad g⁻¹ n) w - w) := by
      rw [h1, map_sub]
    rw [h2]
    exact D.a_mem_fix g (hw2 _)

end RankOneData

end CFSG.RankThree.GF2n.Smith81.S81V
