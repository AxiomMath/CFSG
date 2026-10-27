module

public import CFSG.Timmesfeld.Transvection.QuadFormBasic
public import Mathlib.Tactic.LinearCombination

public section

namespace CFSG.Timmesfeld.Transvection.QuadForm

open QuadraticMap Module

variable {K F : Type*} [Field K] [Field F] (j : K →+* F) (σ : F →+* F)

theorem exists_add_mul_eq (hσ : ∀ z, σ (σ z) = z) (hj : ∀ k, σ (j k) = j k)
    (hfix : ∀ z, σ z = z → ∃ k, j k = z) {θ : F} (hθ : σ θ ≠ θ) (z : F) :
    ∃ a b : K, j a + j b * θ = z := by
  have hδ : θ - σ θ ≠ 0 := sub_ne_zero.2 (Ne.symm hθ)
  obtain ⟨b, hb⟩ := hfix ((z - σ z) / (θ - σ θ)) (by
    rw [map_div₀, map_sub, map_sub, hσ, hσ, ← neg_sub z, ← neg_sub θ, neg_div_neg_eq])
  obtain ⟨a, ha⟩ := hfix (z - j b * θ) (by
    rw [map_sub, map_mul, hj, hb]
    field_simp
    ring)
  exact ⟨a, b, by rw [ha]; ring⟩

theorem eq_zero_of_add_mul_eq_zero {θ : F} (hθ : ∀ k, j k ≠ θ) {a b : K}
    (h : j a + j b * θ = 0) : a = 0 ∧ b = 0 := by
  have hb : b = 0 := by
    by_contra hb
    have hb' : j b ≠ 0 := (map_ne_zero j).2 hb
    apply hθ (-(a / b))
    rw [map_neg, map_div₀]
    field_simp
    linear_combination -h
  subst hb
  rw [map_zero, zero_mul, add_zero, map_eq_zero] at h
  exact ⟨h, rfl⟩

variable [Finite K] [CharP K 2]

theorem exists_mul_self_sub_eq (hj : ∀ k, σ (j k) = j k) (hfix : ∀ z, σ z = z → ∃ k, j k = z)
    {τ : F} (hτ : τ + σ τ = 1) (μ : K) : ∃ s : F, s * s - s = j μ := by
  have h2F : (2 : F) = 0 := by
    rw [← map_ofNat j 2, CharTwo.two_eq_zero, map_zero]
  let φ : K →+ K :=
    { toFun := fun x => x * x - x
      map_zero' := by simp
      map_add' := fun x y => by rw [CharTwo.add_mul_self]; ring }
  have hφ : ∀ x, φ x = x * x - x := fun _ => rfl
  have hker : ∀ x, x ∈ φ.ker ↔ x ∈ ({0, 1} : Set K) := fun x => by
    rw [AddMonoidHom.mem_ker, Set.mem_insert_iff, Set.mem_singleton_iff, hφ,
      show x * x - x = x * (x - 1) by ring, mul_eq_zero, sub_eq_zero]
  have hcard : Nat.card φ.ker = 2 := by
    rw [Nat.card_congr (Equiv.subtypeEquivRight hker), Nat.card_coe_set_eq,
      Set.ncard_pair zero_ne_one]
  have hidx : φ.range.index = 2 := by
    have h1 := AddSubgroup.card_ker_mul_card_range φ
    have h2 := AddSubgroup.card_mul_index φ.range
    rw [hcard] at h1
    have hpos : 0 < Nat.card φ.range := Nat.card_pos
    exact Nat.eq_of_mul_eq_mul_left hpos (by rw [h2, ← h1, mul_comm])
  have hστ : σ τ = 1 - τ := by rw [← hτ]; ring
  obtain ⟨μ₀, hμ₀⟩ := hfix (τ * τ - τ) (by rw [map_sub, map_mul, hστ]; ring)
  have hμ₀R : μ₀ ∉ φ.range := by
    rintro ⟨k, hk⟩
    have hk' : j k * j k - j k = τ * τ - τ := by
      rw [← hμ₀, ← hk, hφ, map_sub, map_mul]
    have hτK : σ τ = τ := by
      have : (τ - j k) * (τ + j k - 1) = 0 := by linear_combination (-1 : F) * hk'
      rcases mul_eq_zero.1 this with h | h
      · rw [sub_eq_zero.1 h, hj]
      · rw [show τ = 1 - j k by linear_combination h, map_sub, map_one, hj]
    have h10 : (1 : F) = 0 := by rw [← hτ, hτK, ← two_mul, h2F, zero_mul]
    exact one_ne_zero h10
  by_cases hμ : μ ∈ φ.range
  · obtain ⟨k, hk⟩ := hμ
    exact ⟨j k, by rw [← hk, hφ, map_sub, map_mul]⟩
  · have hmem : μ + -μ₀ ∈ φ.range := by
      rw [AddSubgroup.add_mem_iff_of_index_two hidx, neg_mem_iff]
      exact iff_of_false hμ hμ₀R
    obtain ⟨k, hk⟩ := hmem
    refine ⟨τ + j k, ?_⟩
    have hk' : j k * j k - j k = j μ + -j μ₀ := by
      rw [← map_neg, ← map_add, ← hk, hφ, map_sub, map_mul]
    linear_combination (-1 : F) * hμ₀ + hk' + τ * j k * h2F

variable {V : Type*} [AddCommGroup V] [Module K V]

theorem exists_addEquiv_of_finrank_eq_two (hσ : ∀ z, σ (σ z) = z)
    (hfix : ∀ z, σ z = z ↔ ∃ k, j k = z) (htr : ∃ τ, τ + σ τ = 1) {Q : QuadraticForm K V}
    (hQ : Q.Anisotropic) (hV : finrank K V = 2) {x₀ : V} (hx₀ : Q x₀ = 1) :
    ∃ ι : F ≃+ V, ι 1 = x₀ ∧ (∀ (k : K) (z : F), ι (j k * z) = k • ι z) ∧
      ∀ z, j (Q (ι z)) = σ z * z := by
  have hj : ∀ k, σ (j k) = j k := fun k => (hfix _).2 ⟨k, rfl⟩
  have hfix' : ∀ z, σ z = z → ∃ k, j k = z := fun z => (hfix z).1
  have hx₀0 : x₀ ≠ 0 := by
    rintro rfl
    rw [QuadraticMap.map_zero] at hx₀
    exact zero_ne_one hx₀
  obtain ⟨w, hw⟩ : ∃ w : V, ∀ c : K, c • x₀ ≠ w := by
    have hne : (K ∙ x₀) ≠ ⊤ := fun h => by
      have h1 := finrank_span_singleton (K := K) hx₀0
      rw [h, finrank_top, hV] at h1
      exact absurd h1 (by norm_num)
    obtain ⟨w, -, hw⟩ := IsConcreteLE.exists_of_lt (lt_top_iff_ne_top.2 hne)
    exact ⟨w, fun c hc => hw (Submodule.mem_span_singleton.2 ⟨c, hc⟩)⟩
  obtain ⟨β, hβ_eq⟩ : ∃ β, polar Q x₀ w = β := ⟨_, rfl⟩
  obtain ⟨γ, hγ_eq⟩ : ∃ γ, Q w = γ := ⟨_, rfl⟩
  have hβ : β ≠ 0 := hβ_eq ▸ polar_ne_zero hQ hx₀0 hw
  obtain ⟨τ, hτ⟩ := htr
  obtain ⟨s, hs⟩ := exists_mul_self_sub_eq j σ hj hfix' hτ (-γ / (β * β))
  obtain ⟨θ, hθ_eq⟩ : ∃ θ, j β * s = θ := ⟨_, rfl⟩
  have hθ : θ * θ - j β * θ + j γ = 0 := by
    have h1 : β * β * (-γ / (β * β)) + γ = 0 := by field_simp; ring
    calc θ * θ - j β * θ + j γ = j β * j β * (s * s - s) + j γ := by rw [← hθ_eq]; ring
      _ = j (β * β * (-γ / (β * β)) + γ) := by rw [hs, map_add, map_mul, map_mul]
      _ = 0 := by rw [h1, map_zero]
  have hθK : ∀ k, j k ≠ θ := fun t ht => by
    have h0 : t * t - β * t + γ = 0 := by
      apply (map_eq_zero j).1
      rw [map_add, map_sub, map_mul, map_mul, ht]
      exact hθ
    have hv : t • x₀ + (-1 : K) • w ≠ 0 := fun h => hw t (by
      rw [neg_one_smul, ← sub_eq_add_neg, sub_eq_zero] at h
      exact h)
    exact hv (hQ _ (by
      rw [apply_smul_add_smul, hx₀, hβ_eq, hγ_eq]
      linear_combination h0))
  have hσθ : σ θ ≠ θ := fun h => by
    obtain ⟨k, hk⟩ := hfix' θ h
    exact hθK k hk
  have hσroot : σ θ * σ θ - j β * σ θ + j γ = 0 := by
    have := congrArg σ hθ
    rwa [map_add, map_sub, map_mul, map_mul, hj, hj, map_zero] at this
  have hsum : θ + σ θ = j β := by
    have h1 : (θ - σ θ) * (θ + σ θ - j β) = 0 := by linear_combination hθ - hσroot
    linear_combination (mul_eq_zero.1 h1).resolve_left (sub_ne_zero.2 (Ne.symm hσθ))
  have hprod : θ * σ θ = j γ := by linear_combination θ * hsum - hθ
  have hdec : ∀ v, ∃ a b : K, a • x₀ + b • w = v := fun v =>
    ⟨_, _, polar_div_smul_add_polar_div_smul hQ hx₀0 hw v⟩
  let ψ : V →+ F :=
    { toFun := fun v => j (polar Q v w / β) + j (polar Q x₀ v / β) * θ
      map_zero' := by simp [polar_zero_left, polar_zero_right]
      map_add' := fun v v' => by
        simp only [polar_add_left, polar_add_right, add_div, map_add]
        ring }
  have hψ : ∀ a b : K, ψ (a • x₀ + b • w) = j a + j b * θ := fun a b => by
    change j (polar Q (a • x₀ + b • w) w / β) + j (polar Q x₀ (a • x₀ + b • w) / β) * θ = _
    simp only [polar_add_left, polar_add_right, polar_smul_left, polar_smul_right,
      polar_self_eq_zero, hβ_eq, smul_eq_mul, mul_zero, add_zero, zero_add,
      mul_div_cancel_right₀ _ hβ]
  have hinj : Function.Injective ψ := by
    rw [injective_iff_map_eq_zero]
    intro v hv
    obtain ⟨a, b, rfl⟩ := hdec v
    rw [hψ] at hv
    obtain ⟨rfl, rfl⟩ := eq_zero_of_add_mul_eq_zero j hθK hv
    simp
  have hsurj : Function.Surjective ψ := fun z => by
    obtain ⟨a, b, rfl⟩ := exists_add_mul_eq j σ hσ hj hfix' hσθ z
    exact ⟨a • x₀ + b • w, hψ a b⟩
  let e := AddEquiv.ofBijective ψ ⟨hinj, hsurj⟩
  have he : ∀ v, e v = ψ v := fun _ => rfl
  have hnorm : ∀ v, j (Q v) = σ (ψ v) * ψ v := fun v => by
    obtain ⟨a, b, rfl⟩ := hdec v
    rw [hψ, apply_smul_add_smul, hx₀, hγ_eq, hβ_eq]
    simp only [map_add, map_mul, map_one, hj]
    linear_combination (-(j a * j b)) * hsum - (j b * j b) * hprod
  refine ⟨e.symm, ?_, fun k z => ?_, fun z => ?_⟩
  · rw [AddEquiv.symm_apply_eq, he]
    have h1 := hψ 1 0
    rw [one_smul, zero_smul, add_zero, map_one, map_zero, zero_mul, add_zero] at h1
    exact h1.symm
  · rw [AddEquiv.symm_apply_eq, he]
    obtain ⟨a, b, hab⟩ := hdec (e.symm z)
    have hz : z = ψ (a • x₀ + b • w) := by rw [hab, ← he, AddEquiv.apply_symm_apply]
    rw [← hab, smul_add, smul_smul, smul_smul, hψ, hz, hψ, map_mul, map_mul]
    ring
  · have h1 := hnorm (e.symm z)
    rwa [← he, AddEquiv.apply_symm_apply] at h1

theorem exists_addEquiv_smul_of_finrank_eq_two (hσ : ∀ z, σ (σ z) = z)
    (hfix : ∀ z, σ z = z ↔ ∃ k, j k = z) (htr : ∃ τ, τ + σ τ = 1) {Q : QuadraticForm K V}
    (hQ : Q.Anisotropic) (hV : finrank K V = 2) {x₀ : V} (hx₀ : x₀ ≠ 0) :
    ∃ ι : F ≃+ V, ι 1 = x₀ ∧ (∀ (k : K) (z : F), ι (j k * z) = k • ι z) ∧
      ∀ z, j (Q (ι z)) = j (Q x₀) * (σ z * z) := by
  have hQx₀ : Q x₀ ≠ 0 := fun h => hx₀ (hQ x₀ h)
  obtain ⟨ι, h1, h2, h3⟩ := exists_addEquiv_of_finrank_eq_two j σ hσ hfix htr
    (Q := (Q x₀)⁻¹ • Q) (fun x hx => hQ x (by
      rw [smul_apply, smul_eq_mul] at hx
      exact (mul_eq_zero.1 hx).resolve_left (inv_ne_zero hQx₀))) hV
    (by rw [smul_apply, smul_eq_mul, inv_mul_cancel₀ hQx₀])
  refine ⟨ι, h1, h2, fun z => ?_⟩
  rw [← h3 z, smul_apply, smul_eq_mul, map_mul, map_inv₀,
    mul_inv_cancel_left₀ ((map_ne_zero j).2 hQx₀)]

end CFSG.Timmesfeld.Transvection.QuadForm
