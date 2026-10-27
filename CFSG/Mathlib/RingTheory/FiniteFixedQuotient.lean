module

public import Mathlib.RingTheory.Smooth.Basic

public noncomputable section

namespace CFSG.CommutativeAlgebra

open scoped BigOperators

theorem smooth_finite_fixed_quotient
    {k A Γ : Type*} [Field k] [CommRing A] [Algebra k A]
    [Group Γ] [Fintype Γ] [Algebra.FiniteType k A] [Algebra.Smooth k A]
    (ρ : Γ →* (A ≃ₐ[k] A)) (hcard : (Fintype.card Γ : k) ≠ 0) :
    Algebra.Smooth k (A ⧸ Ideal.span
      (Set.range fun p : Γ × A => ρ p.1 p.2 - p.2)) := by
  classical
  let I : Ideal A := Ideal.span (Set.range fun p : Γ × A => ρ p.1 p.2 - p.2)
  let π : A →ₐ[k] A ⧸ I := Ideal.Quotient.mkₐ k I
  have hπ (g : Γ) (a : A) : π (ρ g a) = π a := by
    change Ideal.Quotient.mk I (ρ g a) = Ideal.Quotient.mk I a
    rw [Ideal.Quotient.eq]
    exact Ideal.subset_span ⟨(g, a), rfl⟩
  have hfs : Algebra.FormallySmooth k (A ⧸ I) := by
    refine Algebra.FormallySmooth.of_comp_surjective ?_
    intro B _ _ N hN g
    let f : A →ₐ[k] B ⧸ N := g.comp π
    obtain ⟨f₀, hf₀⟩ :=
      Algebra.FormallySmooth.comp_surjective (R := k) (A := A) (B := B) N hN f
    have hf₀_apply (a : A) : Ideal.Quotient.mk N (f₀ a) = f a := by
      simpa only [AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk] using AlgHom.congr_fun hf₀ a
    have hfρ (x : Γ) (a : A) : f (ρ x a) = f a := by
      change g (π (ρ x a)) = g (π a)
      rw [hπ]
    let δg (x : Γ) : A →ₗ[k] B :=
      (f₀.comp (ρ x).toAlgHom).toLinearMap - f₀.toLinearMap
    let δ : A →ₗ[k] B := ∑ x : Γ, δg x
    have hδg_apply (x : Γ) (a : A) : δg x a = f₀ (ρ x a) - f₀ a := by
      rfl
    have hδ_apply (a : A) : δ a = ∑ x : Γ, δg x a := by
      simp only [δ, LinearMap.sum_apply]
    have hδg_mem (x : Γ) (a : A) : δg x a ∈ N := by
      rw [hδg_apply]
      apply Ideal.Quotient.eq.mp
      exact (hf₀_apply (ρ x a)).trans ((hfρ x a).trans (hf₀_apply a).symm)
    have hδ_mem (a : A) : δ a ∈ N := by
      rw [hδ_apply]
      exact N.sum_mem fun x _ => hδg_mem x a
    have hδg_mul (x : Γ) (a b : A) :
        δg x (a * b) = f₀ a * δg x b + f₀ b * δg x a := by
      have hz : δg x a * δg x b = 0 := by
        have hm : δg x a * δg x b ∈ N ^ 2 := by
          rw [pow_two]
          exact Ideal.mul_mem_mul (hδg_mem x a) (hδg_mem x b)
        rw [hN] at hm
        exact Ideal.mem_bot.mp hm
      rw [hδg_apply, hδg_apply, hδg_apply]
      simp only [map_mul]
      rw [hδg_apply, hδg_apply] at hz
      calc
        f₀ (ρ x a) * f₀ (ρ x b) - f₀ a * f₀ b =
            f₀ a * (f₀ (ρ x b) - f₀ b) + f₀ b * (f₀ (ρ x a) - f₀ a) +
              (f₀ (ρ x a) - f₀ a) * (f₀ (ρ x b) - f₀ b) := by ring
        _ = f₀ a * (f₀ (ρ x b) - f₀ b) + f₀ b * (f₀ (ρ x a) - f₀ a) := by
          rw [hz, add_zero]
    have hδ_mul (a b : A) : δ (a * b) = f₀ a * δ b + f₀ b * δ a := by
      rw [hδ_apply, hδ_apply, hδ_apply, Finset.mul_sum, Finset.mul_sum,
        ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro x _
      exact hδg_mul x a b
    have hδ_one : δ 1 = 0 := by
      rw [hδ_apply]
      simp only [hδg_apply, map_one, sub_self, Finset.sum_const_zero]
    let n := Fintype.card Γ
    let r : k := (n : k)⁻¹
    let c : B := algebraMap k B r
    have hc : (n : B) * c = 1 := by
      have hn : (n : B) = algebraMap k B (n : k) := (map_natCast (algebraMap k B) n).symm
      rw [hn]
      change algebraMap k B (n : k) * algebraMap k B r = 1
      rw [← map_mul, mul_inv_cancel₀ hcard, map_one]
    have hc' : c * (n : B) = 1 := (mul_comm c (n : B)).trans hc
    let Flinear : A →ₗ[k] B := f₀.toLinearMap + r • δ
    have hF_one : Flinear 1 = 1 := by
      change f₀ 1 + r • δ 1 = 1
      rw [hδ_one, map_one, smul_zero, add_zero]
    have hF_mul (a b : A) : Flinear (a * b) = Flinear a * Flinear b := by
      have hz : δ a * δ b = 0 := by
        have hm : δ a * δ b ∈ N ^ 2 := by
          rw [pow_two]
          exact Ideal.mul_mem_mul (hδ_mem a) (hδ_mem b)
        rw [hN] at hm
        exact Ideal.mem_bot.mp hm
      change f₀ (a * b) + r • δ (a * b) = (f₀ a + r • δ a) * (f₀ b + r • δ b)
      simp only [Algebra.smul_def]
      rw [hδ_mul, map_mul]
      change f₀ a * f₀ b + c * (f₀ a * δ b + f₀ b * δ a) =
        (f₀ a + c * δ a) * (f₀ b + c * δ b)
      calc
        f₀ a * f₀ b + c * (f₀ a * δ b + f₀ b * δ a) =
            (f₀ a + c * δ a) * (f₀ b + c * δ b) - c * c * (δ a * δ b) := by ring
        _ = (f₀ a + c * δ a) * (f₀ b + c * δ b) := by rw [hz, mul_zero, sub_zero]
    let F : A →ₐ[k] B := AlgHom.ofLinearMap Flinear hF_one hF_mul
    have hF_apply (a : A) : F a = f₀ a + c * δ a := by
      change f₀ a + r • δ a = _
      rw [Algebra.smul_def]
    have hF_average (a : A) : F a = c * ∑ x : Γ, f₀ (ρ x a) := by
      rw [hF_apply, hδ_apply]
      simp only [hδg_apply]
      rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      change f₀ a + c * ((∑ x : Γ, f₀ (ρ x a)) - (n : B) * f₀ a) = _
      calc
        f₀ a + c * ((∑ x : Γ, f₀ (ρ x a)) - (n : B) * f₀ a) =
            c * (∑ x : Γ, f₀ (ρ x a)) + (1 - c * (n : B)) * f₀ a := by ring
        _ = c * ∑ x : Γ, f₀ (ρ x a) := by rw [hc', sub_self, zero_mul, add_zero]
    have hF_fixed (x : Γ) (a : A) : F (ρ x a) = F a := by
      rw [hF_average, hF_average]
      congr 1
      apply Fintype.sum_equiv (Equiv.mulRight x)
      intro y
      change f₀ (ρ y (ρ x a)) = f₀ (ρ (y * x) a)
      rw [map_mul, AlgEquiv.mul_apply]
    have hF_I (a : A) (ha : a ∈ I) : F a = 0 := by
      have hker : I ≤ RingHom.ker F.toRingHom := by
        rw [Ideal.span_le]
        rintro _ ⟨⟨x, b⟩, rfl⟩
        change F (ρ x b - b) = 0
        rw [map_sub, hF_fixed, sub_self]
      exact hker ha
    let g₁ : A ⧸ I →ₐ[k] B := Ideal.Quotient.liftₐ I F hF_I
    have hg₁ (a : A) : g₁ (π a) = F a :=
      AlgHom.congr_fun (Ideal.Quotient.liftₐ_comp I F hF_I) a
    have hF_mk (a : A) : (Ideal.Quotient.mkₐ k N) (F a) = f a := by
      rw [hF_apply, map_add, map_mul]
      have hd : (Ideal.Quotient.mkₐ k N) (δ a) = 0 :=
        Ideal.Quotient.eq_zero_iff_mem.mpr (hδ_mem a)
      rw [hd, mul_zero, add_zero]
      exact hf₀_apply a
    refine ⟨g₁, ?_⟩
    apply Ideal.Quotient.algHom_ext
    apply AlgHom.ext
    intro a
    simp only [AlgHom.comp_apply]
    rw [hg₁ a, hF_mk a]
    rfl
  have hfp : Algebra.FinitePresentation k (A ⧸ I) :=
    Algebra.FinitePresentation.of_finiteType.mp (inferInstance : Algebra.FiniteType k (A ⧸ I))
  exact ⟨hfs, hfp⟩

theorem smooth_finite_order_fixed_quotient
    {k A : Type*} [Field k] [CommRing A] [Algebra k A]
    [Algebra.FiniteType k A] [Algebra.Smooth k A]
    (σ : A ≃ₐ[k] A) (n : ℕ) (hcard : (n : k) ≠ 0) (hσ : σ ^ n = 1) :
    Algebra.Smooth k (A ⧸ Ideal.span (Set.range fun a : A => σ a - a)) := by
  classical
  have hn : n ≠ 0 := by
    intro hn
    subst n
    exact hcard Nat.cast_zero
  have hfin : IsOfFinOrder σ := isOfFinOrder_iff_pow_eq_one.mpr ⟨n, Nat.pos_of_ne_zero hn, hσ⟩
  let Γ := Subgroup.zpowers σ
  let : Finite Γ := (finite_zpowers).mpr hfin
  let : Fintype Γ := Fintype.ofFinite Γ
  let ρ : Γ →* (A ≃ₐ[k] A) := (Subgroup.zpowers σ).subtype
  have hdiv : Fintype.card Γ ∣ n := by
    change Fintype.card (Subgroup.zpowers σ) ∣ n
    rw [← Nat.card_eq_fintype_card, Nat.card_zpowers]
    exact orderOf_dvd_of_pow_eq_one hσ
  have hΓ : (Fintype.card Γ : k) ≠ 0 := by
    intro h
    obtain ⟨q, hq⟩ := hdiv
    apply hcard
    rw [hq, Nat.cast_mul, h, zero_mul]
  let I : Ideal A := Ideal.span (Set.range fun a : A => σ a - a)
  let π : A →ₐ[k] A ⧸ I := Ideal.Quotient.mkₐ k I
  have hπ (a : A) : π (σ a) = π a := by
    change Ideal.Quotient.mk I (σ a) = Ideal.Quotient.mk I a
    rw [Ideal.Quotient.eq]
    exact Ideal.subset_span ⟨a, rfl⟩
  let P : Subgroup (A ≃ₐ[k] A) :=
    { carrier := {e | ∀ a, π (e a) = π a}
      one_mem' := by intro a; simp
      mul_mem' := by
        intro e f he hf a
        rw [AlgEquiv.mul_apply, he, hf]
      inv_mem' := by
        intro e he a
        have h := he (e.symm a)
        rw [e.apply_symm_apply] at h
        exact h.symm }
  have hle : Subgroup.zpowers σ ≤ P := Subgroup.zpowers_le_of_mem hπ
  have hI : Ideal.span (Set.range fun p : Γ × A => ρ p.1 p.2 - p.2) = I := by
    apply le_antisymm
    · rw [Ideal.span_le]
      rintro _ ⟨⟨x, a⟩, rfl⟩
      apply Ideal.Quotient.eq_zero_iff_mem.mp
      change π (ρ x a - a) = 0
      rw [map_sub]
      have hx := hle x.property
      change ∀ b : A, π (x.val b) = π b at hx
      change π (x.val a) - π a = 0
      rw [hx a, sub_self]
    · rw [Ideal.span_le]
      rintro _ ⟨a, rfl⟩
      exact Ideal.subset_span ⟨(⟨σ, Subgroup.mem_zpowers σ⟩, a), rfl⟩
  have h := smooth_finite_fixed_quotient ρ hΓ
  rw [hI] at h
  exact h

end CFSG.CommutativeAlgebra
