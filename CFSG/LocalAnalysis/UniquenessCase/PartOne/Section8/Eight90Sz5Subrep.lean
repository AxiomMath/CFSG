module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight90Sz5Defs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Sz5

open Subgroup

theorem sz5e1_irreducible_subrep {F : Type} [Field F] (hF : ringChar F ≠ 2)
    {K : Type} [Group K] [Finite K] (R : Subgroup K) [R.Normal]
    (hR : IsPGroup 2 R) {A : Type} [AddCommGroup A] [Module F A]
    [Module.Finite F A] (ρ : K →* (A ≃ₗ[F] A)) (hnt : ∃ r ∈ R, ∃ v, ρ r v ≠ v) :
    ∃ (B : Submodule F A) (σ : K →* (↥B ≃ₗ[F] ↥B)),
      (∀ (k : K) (b : ↥B), ((σ k b : ↥B) : A) = ρ k b) ∧ IsIrreducibleRep σ ∧
      ∃ r ∈ R, ∃ b : ↥B, σ r b ≠ b := by
  classical
  have : Fintype R := Fintype.ofFinite R
  let n : F := (Fintype.card R : F)
  have hn0 : n ≠ 0 := by
    obtain ⟨m, hm⟩ := hR.exists_card_eq
    have hcard : Fintype.card R = 2 ^ m := by
      rw [← Nat.card_eq_fintype_card]
      exact hm
    have : n = (2 : F) ^ m := by
      show (Fintype.card R : F) = _
      rw [hcard, Nat.cast_pow]
      norm_num
    rw [this]
    exact pow_ne_zero m (Ring.two_ne_zero hF)
  let e : A →ₗ[F] A := n⁻¹ • ∑ r : R, (ρ (r : K) : A →ₗ[F] A)
  have he_apply : ∀ v : A, e v = n⁻¹ • ∑ r : R, ρ (r : K) v := by
    intro v
    simp only [e, LinearMap.smul_apply, LinearMap.sum_apply, LinearEquiv.coe_coe]
  have hleft : ∀ r : R, ∀ v : A, ρ (r : K) (e v) = e v := by
    intro r v
    rw [he_apply, map_smul, map_sum]
    congr 1
    have h1 : (∑ s : R, ρ (r : K) (ρ (s : K) v)) = ∑ s : R, ρ ((r * s : R) : K) v := by
      apply Finset.sum_congr rfl
      intro s _
      rw [← LinearEquiv.mul_apply, ← map_mul, Subgroup.coe_mul]
    rw [h1]
    exact Equiv.sum_comp (Equiv.mulLeft r) (fun s : R => ρ (s : K) v)
  have he_idem : e.comp e = e := by
    ext v
    rw [LinearMap.comp_apply]
    rw [show e (e v) = n⁻¹ • ∑ r : R, ρ (r : K) (e v) from he_apply (e v)]
    have hsum : (∑ r : R, ρ (r : K) (e v)) = (Fintype.card R : F) • e v := by
      rw [Finset.sum_congr rfl (fun r _ => hleft r v), Finset.sum_const, Finset.card_univ,
        ← Nat.cast_smul_eq_nsmul (F)]
    rw [hsum, smul_smul]
    have hc : (Fintype.card R : F) = n := rfl
    rw [hc, inv_mul_cancel₀ hn0, one_smul]
  have he_idem' : ∀ v : A, e (e v) = e v := fun v => LinearMap.congr_fun he_idem v
  have hfix : ∀ v : A, (∀ r : R, ρ (r : K) v = v) → e v = v := by
    intro v hv
    rw [he_apply]
    have hsum : (∑ r : R, ρ (r : K) v) = (Fintype.card R : F) • v := by
      rw [Finset.sum_congr rfl (fun r _ => hv r), Finset.sum_const, Finset.card_univ,
        ← Nat.cast_smul_eq_nsmul (F)]
    rw [hsum, smul_smul]
    have hc : (Fintype.card R : F) = n := rfl
    rw [hc, inv_mul_cancel₀ hn0, one_smul]
  have hmul : ∀ (a b : K) (w : A), ρ a (ρ b w) = ρ (a * b) w := by
    intro a b w
    rw [← LinearEquiv.mul_apply, ← map_mul]
  have hconj : ∀ k : K, (ρ k : A →ₗ[F] A).comp (e.comp (ρ (k⁻¹) : A →ₗ[F] A)) = e := by
    intro k
    ext v
    rw [LinearMap.comp_apply, LinearMap.comp_apply]
    calc ρ (k : K) (e (ρ (k⁻¹) v))
        = ρ (k : K) (n⁻¹ • ∑ r : R, ρ (r : K) (ρ (k⁻¹) v)) := by rw [he_apply]
      _ = n⁻¹ • ∑ r : R, ρ (k : K) (ρ (r : K) (ρ (k⁻¹) v)) := by rw [map_smul, map_sum]
      _ = n⁻¹ • ∑ r : R, ρ ((MulAut.conjNormal k) r : K) v := by
            congr 1
            apply Finset.sum_congr rfl
            intro r _
            rw [hmul k (r : K) (ρ (k⁻¹) v), hmul (k * (r : K)) (k⁻¹) v,
              MulAut.conjNormal_apply]
      _ = n⁻¹ • ∑ s : R, ρ (s : K) v := by
            congr 1
            exact Equiv.sum_comp (MulAut.conjNormal k).toEquiv (fun s : R => ρ (s : K) v)
      _ = e v := (he_apply v).symm
  have hcomm : ∀ k : K, ∀ v : A, ρ (k : K) (e v) = e (ρ (k : K) v) := by
    intro k v
    have h := LinearMap.congr_fun (hconj k) (ρ (k : K) v)
    simpa using h
  let A₁ : Submodule F A := LinearMap.ker e
  have hA₁inv : ∀ k : K, ∀ u ∈ A₁, ρ (k : K) u ∈ A₁ := by
    intro k u hu
    rw [LinearMap.mem_ker] at hu ⊢
    rw [← hcomm k u, hu, map_zero]
  obtain ⟨r0, hr0, v0, hv0⟩ := hnt
  let r0' : R := ⟨r0, hr0⟩
  let w : A := v0 - e v0
  have hw_mem : w ∈ A₁ := by
    rw [LinearMap.mem_ker]
    show e (v0 - e v0) = 0
    rw [map_sub, he_idem', sub_self]
  have hw_ne : w ≠ 0 := by
    intro hw0
    have hfix0 : ρ (r0 : K) (e v0) = e v0 := hleft r0' v0
    have hdiff : ρ (r0 : K) w - w = ρ (r0 : K) v0 - v0 := by
      simp only [w, map_sub, hfix0]
      abel
    apply (sub_ne_zero.mpr hv0)
    rw [← hdiff, hw0, map_zero, sub_self]
  let S : Submodule F A := Submodule.span F (Set.range fun k : K => ρ (k : K) w)
  have hwS : w ∈ S := by
    apply Submodule.subset_span
    exact ⟨1, by simp⟩
  have hS_ne : S ≠ ⊥ := by
    intro hbot
    have : w ∈ (⊥ : Submodule F A) := hbot ▸ hwS
    exact hw_ne (by simpa using this)
  have hS_le : S ≤ A₁ := by
    apply Submodule.span_le.mpr
    rintro x ⟨k, rfl⟩
    exact hA₁inv k w hw_mem
  have hS_inv : ∀ k : K, ∀ u ∈ S, ρ (k : K) u ∈ S := by
    intro k u hu
    refine Submodule.span_induction
      (p := fun u _ => ρ (k : K) u ∈ S) ?_ ?_ ?_ ?_ hu
    · rintro x ⟨k', rfl⟩
      rw [← LinearEquiv.mul_apply, ← map_mul]
      exact Submodule.subset_span ⟨k * k', rfl⟩
    · simp
    · intro x y hx hy ihx ihy
      rw [map_add]
      exact S.add_mem ihx ihy
    · intro c x hx ih
      rw [map_smul]
      exact S.smul_mem c ih
  let P : Submodule F A → Prop :=
    fun W => W ≤ A₁ ∧ (∀ k : K, ∀ u ∈ W, ρ (k : K) u ∈ W) ∧ W ≠ ⊥
  have hexP : ∃ W, P W := ⟨S, hS_le, hS_inv, hS_ne⟩
  have hex : ∃ d : ℕ, ∃ W : Submodule F A, P W ∧ Module.finrank F W = d := by
    obtain ⟨W, hW⟩ := hexP
    exact ⟨Module.finrank F W, W, hW, rfl⟩
  obtain ⟨B, hPB, hBdim⟩ := Nat.find_spec hex
  obtain ⟨hB_le, hB_inv, hB_ne⟩ := hPB
  have hmin : ∀ W : Submodule F A, P W → Nat.find hex ≤ Module.finrank F W := by
    intro W hW
    by_contra hlt
    push Not at hlt
    exact Nat.find_min hex hlt ⟨W, hW, rfl⟩
  let restrict : (k : K) → (↥B →ₗ[F] ↥B) := fun k =>
    { toFun := fun b => ⟨ρ (k : K) (b : A), hB_inv k (b : A) b.2⟩
      map_add' := by
        intro x y
        apply Subtype.ext
        simp [map_add]
      map_smul' := by
        intro c x
        apply Subtype.ext
        simp [map_smul] }
  have hrestrict_coe : ∀ (k : K) (b : ↥B), ((restrict k b : ↥B) : A) = ρ (k : K) (b : A) :=
    fun k b => rfl
  have hrestrict_bij : ∀ k : K, Function.Bijective (restrict k) := by
    intro k
    constructor
    · intro x y hxy
      apply Subtype.ext
      have h := congrArg (fun z : ↥B => (z : A)) hxy
      simp only [hrestrict_coe] at h
      exact (ρ (k : K)).injective h
    · intro y
      refine ⟨⟨ρ (k⁻¹ : K) (y : A), hB_inv (k⁻¹) (y : A) y.2⟩, ?_⟩
      apply Subtype.ext
      simp only [hrestrict_coe]
      rw [← LinearEquiv.mul_apply, ← map_mul]
      simp
  let σfun : K → (↥B ≃ₗ[F] ↥B) := fun k =>
    LinearEquiv.ofBijective (restrict k) (hrestrict_bij k)
  have hσ_coe : ∀ (k : K) (b : ↥B), ((σfun k b : ↥B) : A) = ρ (k : K) (b : A) := by
    intro k b
    rw [show (σfun k) b = restrict k b from LinearEquiv.ofBijective_apply _ _]
    exact hrestrict_coe k b
  let σ : K →* (↥B ≃ₗ[F] ↥B) :=
    { toFun := σfun
      map_one' := by
        ext b
        simp only [hσ_coe]
        simp
      map_mul' := by
        intro k l
        ext b
        simp only [hσ_coe, LinearEquiv.mul_apply]
        rw [map_mul]
        rfl }
  have hσ_coe' : ∀ (k : K) (b : ↥B), ((σ k b : ↥B) : A) = ρ (k : K) (b : A) := hσ_coe
  have hirr : IsIrreducibleRep σ := by
    intro W' hW'
    by_cases hbot : W' = ⊥
    · exact Or.inl hbot
    · right
      let W : Submodule F A := W'.map B.subtype
      have hWle : W ≤ B := Submodule.map_subtype_le B W'
      have hWleA : W ≤ A₁ := hWle.trans hB_le
      have hWinv : ∀ k : K, ∀ u ∈ W, ρ (k : K) u ∈ W := by
        intro k u hu
        rw [Submodule.mem_map] at hu ⊢
        obtain ⟨b, hb, rfl⟩ := hu
        exact ⟨σ k b, hW' k b hb, (hσ_coe' k b).symm⟩
      have hWne : W ≠ ⊥ := by
        intro hWbot
        apply hbot
        rw [Submodule.eq_bot_iff] at hWbot ⊢
        intro b hb
        have hmem : (b : A) ∈ W := ⟨b, hb, rfl⟩
        apply Subtype.ext
        exact hWbot (b : A) hmem
      have hPW : P W := ⟨hWleA, hWinv, hWne⟩
      have hdW : Nat.find hex ≤ Module.finrank F W := hmin W hPW
      have hleW : Module.finrank F W ≤ Module.finrank F B :=
        Submodule.finrank_mono hWle
      have hdim : Module.finrank F W = Module.finrank F B := by
        omega
      have hWB : W = B := Submodule.eq_of_le_of_finrank_eq hWle hdim
      have hmaps : W'.map B.subtype = (⊤ : Submodule F ↥B).map B.subtype := by
        rw [show W'.map B.subtype = W from rfl, hWB, Submodule.map_subtype_top]
      exact Submodule.map_injective_of_injective B.subtype_injective hmaps
  have hRnt : ∃ r ∈ R, ∃ b : ↥B, σ r b ≠ b := by
    by_contra h
    push Not at h
    have hBbot : B = ⊥ := by
      rw [Submodule.eq_bot_iff]
      intro b hb
      have hfixb : ∀ r : R, ρ (r : K) b = b := by
        intro r
        have h1 := h (r : K) r.2 ⟨b, hb⟩
        have h2 := congrArg (fun z : ↥B => (z : A)) h1
        rwa [hσ_coe'] at h2
      have heb : e b = b := hfix b hfixb
      have heb0 : e b = 0 := by
        have : b ∈ LinearMap.ker e := hB_le hb
        exact this
      exact heb.symm.trans heb0
    exact hB_ne hBbot
  exact ⟨B, σ, hσ_coe', hirr, hRnt⟩

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Sz5
