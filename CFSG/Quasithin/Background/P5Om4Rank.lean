module

public import CFSG.Quasithin.Background.P3OrthoOm4

public section

open Matrix CFSG.Assembly.LowTwoRank CFSG.ComponentClassification.CatalogueBOrthogonalFourSplit

namespace CFSG.Quasithin

namespace G11

namespace P5

section Minor

variable {K : Type} [Field K]

theorem linearIndependent_pair_of_minor {N : Type} [AddCommGroup N] [Module K N]
    (φ₁ φ₂ : N →ₗ[K] K) (u w : N) (h : φ₁ u * φ₂ w - φ₂ u * φ₁ w ≠ 0) :
    LinearIndependent K ![u, w] := by
  rw [LinearIndependent.pair_iff]
  intro s t hst
  have h1 := congrArg φ₁ hst
  have h2 := congrArg φ₂ hst
  simp only [map_add, map_smul, smul_eq_mul, map_zero] at h1 h2
  constructor
  · apply (mul_eq_zero.1 (?_ : s * (φ₁ u * φ₂ w - φ₂ u * φ₁ w) = 0)).resolve_right h
    linear_combination (φ₂ w) * h1 - (φ₁ w) * h2
  · apply (mul_eq_zero.1 (?_ : t * (φ₁ u * φ₂ w - φ₂ u * φ₁ w) = 0)).resolve_right h
    linear_combination (φ₁ u) * h2 - (φ₂ u) * h1

theorem two_le_finrank_range_of_minor {M N : Type} [AddCommGroup M] [Module K M]
    [AddCommGroup N] [Module K N] [Module.Finite K N] (T : M →ₗ[K] N) (φ₁ φ₂ : N →ₗ[K] K)
    (x y : M) (h : φ₁ (T x) * φ₂ (T y) - φ₂ (T x) * φ₁ (T y) ≠ 0) :
    2 ≤ Module.finrank K (LinearMap.range T) := by
  have hli := linearIndependent_pair_of_minor φ₁ φ₂ (T x) (T y) h
  have hle : Submodule.span K (Set.range ![T x, T y]) ≤ LinearMap.range T := by
    rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    fin_cases i
    · exact ⟨x, rfl⟩
    · exact ⟨y, rfl⟩
  have := Submodule.finrank_mono hle
  rw [finrank_span_eq_card hli] at this
  simpa using this

@[expose] def lrSub (A B : Matrix (Fin 2) (Fin 2) K) :
    Matrix (Fin 2) (Fin 2) K →ₗ[K] Matrix (Fin 2) (Fin 2) K where
  toFun X := A * X * B - X
  map_add' X Y := by simp only [Matrix.mul_add, Matrix.add_mul]; abel
  map_smul' c X := by simp [smul_sub]

theorem lrSub_apply (A B X : Matrix (Fin 2) (Fin 2) K) : lrSub A B X = A * X * B - X := rfl

theorem two_le_finrank_lrSub (A B x y : Matrix (Fin 2) (Fin 2) K) (k l k' l' : Fin 2)
    (h : (lrSub A B x) k l * (lrSub A B y) k' l' - (lrSub A B x) k' l' * (lrSub A B y) k l ≠ 0) :
    2 ≤ Module.finrank K (LinearMap.range (lrSub A B)) :=
  two_le_finrank_range_of_minor (lrSub A B) (Matrix.entryLinearMap K K k l)
    (Matrix.entryLinearMap K K k' l') x y (by simpa using h)

variable [CharP K 2]

theorem eq_one_of_mul_self_eq_one {x : K} (h : x * x = 1) : x = 1 := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have : (x - 1) ^ 2 = 0 := by linear_combination h - (x - 1) * h2
  exact sub_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1 this)

theorem rank_ge_two (a b c d p q r s : K) (hA : a * d - b * c = 1) (hB : p * s - q * r = 1)
    (hne : ¬ (a = 1 ∧ b = 0 ∧ c = 0 ∧ d = 1 ∧ p = 1 ∧ q = 0 ∧ r = 0 ∧ s = 1)) :
    2 ≤ Module.finrank K (LinearMap.range (lrSub !![a, b; c, d] !![p, q; r, s])) := by
  by_cases hc : c = 0
  · by_cases hq : q = 0
    · by_cases hr : r = 0
      · by_cases hb : b = 0
        · subst hc hq hr hb
          have hA' : a * d = 1 := by simpa using hA
          have hB' : p * s = 1 := by simpa using hB
          by_cases hap : a * p = 1
          · have hsa : s = a := by linear_combination (-s) * hap + a * hB'
            have hdp : d = p := by linear_combination (-d) * hap + p * hA'
            have ha1 : a ≠ 1 := by
              intro ha
              have hp : p = 1 := by simpa [ha] using hap
              exact hne ⟨ha, rfl, rfl, by rw [hdp, hp], hp, rfl, rfl, by rw [hsa, ha]⟩
            have hp1 : p ≠ 1 := by
              intro hp
              exact ha1 (by simpa [hp] using hap)
            have ha2 : a * a ≠ 1 := fun h => ha1 (eq_one_of_mul_self_eq_one h)
            have hp2 : p * p ≠ 1 := fun h => hp1 (eq_one_of_mul_self_eq_one h)
            refine two_le_finrank_lrSub _ _ !![0, 1; 0, 0] !![0, 0; 1, 0] 0 1 1 0 ?_
            simp only [lrSub_apply, Matrix.mul_fin_two, hsa, hdp]
            simp [sub_eq_zero, ha2, hp2]
          · have hds : d * s ≠ 1 := by
              intro hds
              exact hap (by linear_combination (-(a * p)) * hds + (p * s) * hA' + hB')
            refine two_le_finrank_lrSub _ _ !![1, 0; 0, 0] !![0, 0; 0, 1] 0 0 1 1 ?_
            simp [lrSub_apply, sub_eq_zero, hap, hds]
        · refine two_le_finrank_lrSub _ _ !![0, 0; 1, 0] !![0, 0; 0, 1] 0 0 0 1 ?_
          have : b * p * (b * s) - b * q * (b * r) = b ^ 2 := by linear_combination b ^ 2 * hB
          simpa [lrSub_apply, this] using hb
      · refine two_le_finrank_lrSub _ _ !![0, 1; 0, 0] !![0, 0; 0, 1] 0 0 1 0 ?_
        have : a * r * (d * r) - c * r * (b * r) = r ^ 2 := by linear_combination r ^ 2 * hA
        simpa [lrSub_apply, this] using hr
    · refine two_le_finrank_lrSub _ _ !![1, 0; 0, 0] !![0, 0; 1, 0] 0 1 1 1 ?_
      have : a * q * (d * q) - c * q * (b * q) = q ^ 2 := by linear_combination q ^ 2 * hA
      simpa [lrSub_apply, this] using hq
  · refine two_le_finrank_lrSub _ _ !![1, 0; 0, 0] !![0, 1; 0, 0] 1 0 1 1 ?_
    have : c * p * (c * s) - c * q * (c * r) = c ^ 2 := by linear_combination c ^ 2 * hB
    simpa [lrSub_apply, this] using hc

theorem rank_ge_two_special (A B : Matrix.SpecialLinearGroup (Fin 2) K) (hne : ¬ (A = 1 ∧ B = 1)) :
    2 ≤ Module.finrank K (LinearMap.range (lrSub (A : Matrix (Fin 2) (Fin 2) K) B)) := by
  have hA : (A : Matrix (Fin 2) (Fin 2) K) 0 0 * (A : Matrix (Fin 2) (Fin 2) K) 1 1 -
      (A : Matrix (Fin 2) (Fin 2) K) 0 1 * (A : Matrix (Fin 2) (Fin 2) K) 1 0 = 1 := by
    have := Matrix.SpecialLinearGroup.det_coe A
    rwa [Matrix.det_fin_two] at this
  have hB : (B : Matrix (Fin 2) (Fin 2) K) 0 0 * (B : Matrix (Fin 2) (Fin 2) K) 1 1 -
      (B : Matrix (Fin 2) (Fin 2) K) 0 1 * (B : Matrix (Fin 2) (Fin 2) K) 1 0 = 1 := by
    have := Matrix.SpecialLinearGroup.det_coe B
    rwa [Matrix.det_fin_two] at this
  have eA := Matrix.eta_fin_two (A : Matrix (Fin 2) (Fin 2) K)
  have eB := Matrix.eta_fin_two (B : Matrix (Fin 2) (Fin 2) K)
  rw [eA, eB]
  refine rank_ge_two _ _ _ _ _ _ _ _ hA hB ?_
  rintro ⟨h00, h01, h10, h11, g00, g01, g10, g11⟩
  refine hne ⟨?_, ?_⟩
  · apply Subtype.ext
    rw [eA]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [h00, h01, h10, h11]
  · apply Subtype.ext
    rw [eB]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [g00, g01, g10, g11]

end Minor

section Omega

variable {K : Type} [Field K]

open P3Ortho.Om4 in
theorem rho'_apply (z : Matrix.SpecialLinearGroup (Fin 2) K × Matrix.SpecialLinearGroup (Fin 2) K)
    (X : Matrix (Fin 2) (Fin 2) K) :
    rho' K z X = z.1.val * X * (z.2⁻¹ : Matrix.SpecialLinearGroup (Fin 2) K).val :=
  specialRho_apply z X

open P3Ortho.Om4 in
theorem two_le_finrank_range_rho [CharP K 2]
    (z : Matrix.SpecialLinearGroup (Fin 2) K × Matrix.SpecialLinearGroup (Fin 2) K) (hz : z ≠ 1) :
    2 ≤ Module.finrank K
      (LinearMap.range (((rho' K z : Matrix (Fin 2) (Fin 2) K ≃ₗ[K] Matrix (Fin 2) (Fin 2) K) :
        Matrix (Fin 2) (Fin 2) K →ₗ[K] Matrix (Fin 2) (Fin 2) K) - LinearMap.id)) := by
  have hrange : (((rho' K z : Matrix (Fin 2) (Fin 2) K ≃ₗ[K] Matrix (Fin 2) (Fin 2) K) :
      Matrix (Fin 2) (Fin 2) K →ₗ[K] Matrix (Fin 2) (Fin 2) K) - LinearMap.id) =
      lrSub (z.1 : Matrix (Fin 2) (Fin 2) K) (z.2⁻¹ : Matrix.SpecialLinearGroup (Fin 2) K) := by
    apply LinearMap.ext
    intro X
    simp [lrSub_apply, rho'_apply]
  rw [hrange]
  refine rank_ge_two_special _ _ ?_
  rintro ⟨h1, h2⟩
  exact hz (Prod.ext h1 (inv_eq_one.1 h2))

end Omega

section Module

variable {K : Type} [Field K] [Finite K] [CharP K 2]

open P3Ortho.Om4 in
theorem exists_rho'_eq (h4 : 4 ≤ Nat.card K) {g : GL (Fin 2 ⊕ Fin 2) K}
    (hg : g ∈ StatedOmega (StatedQuadPlus 2 K)) : ∃ z, rho' K z = Ψ K g := by
  have h1 : Ψ K g ∈ (StatedOmega (StatedQuadPlus 2 K)).map (Ψ K).toMonoidHom := ⟨g, hg, rfl⟩
  rw [map_statedOmega, commutator_eq_range h4] at h1
  exact MonoidHom.mem_range.1 h1

open P3Ortho.Om4 in
theorem two_le_finrank_range_omega (h4 : 4 ≤ Nat.card K) {g : GL (Fin 2 ⊕ Fin 2) K}
    (hg : g ∈ StatedOmega (StatedQuadPlus 2 K)) (hne : g ≠ 1) :
    2 ≤ Module.finrank K
      (LinearMap.range (((Ψ K g : Matrix (Fin 2) (Fin 2) K ≃ₗ[K] Matrix (Fin 2) (Fin 2) K) :
        Matrix (Fin 2) (Fin 2) K →ₗ[K] Matrix (Fin 2) (Fin 2) K) - LinearMap.id)) := by
  obtain ⟨z, hz⟩ := exists_rho'_eq h4 hg
  have hz1 : z ≠ 1 := by
    rintro rfl
    apply hne
    rw [map_one] at hz
    exact (Ψ K).injective (by rw [← hz, map_one])
  rw [← hz]
  exact two_le_finrank_range_rho z hz1

open P3Ortho.Om4 in
theorem finrank_range_sub_one_ge [Algebra (ZMod 2) K] (h4 : 4 ≤ Nat.card K) {V : Type}
    [AddCommGroup V] [Module (ZMod 2) V] (ψ : V ≃ₗ[ZMod 2] (Fin 2 ⊕ Fin 2 → K))
    (a : V ≃ₗ[ZMod 2] V) {g : GL (Fin 2 ⊕ Fin 2) K} (hg : g ∈ StatedOmega (StatedQuadPlus 2 K))
    (hne : g ≠ 1)
    (h : ∀ v, ψ (a v) = (g : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ ψ v) :
    2 * Module.finrank (ZMod 2) K ≤
      Module.finrank (ZMod 2) (LinearMap.range (a.toLinearMap - LinearMap.id)) := by
  let θ : V ≃ₗ[ZMod 2] Matrix (Fin 2) (Fin 2) K :=
    ψ.trans ((toMat K).restrictScalars (ZMod 2))
  have hθ : ∀ v, θ (a v) = Ψ K g (θ v) := by
    intro v
    simp [θ, h, Ψ_apply]
  let T : Matrix (Fin 2) (Fin 2) K →ₗ[K] Matrix (Fin 2) (Fin 2) K :=
    ((Ψ K g : Matrix (Fin 2) (Fin 2) K ≃ₗ[K] Matrix (Fin 2) (Fin 2) K) :
      Matrix (Fin 2) (Fin 2) K →ₗ[K] Matrix (Fin 2) (Fin 2) K) - LinearMap.id
  have hmap : (LinearMap.range (a.toLinearMap - LinearMap.id)).map (θ : V →ₗ[ZMod 2] _) =
      (LinearMap.range T).restrictScalars (ZMod 2) := by
    ext w
    constructor
    · rintro ⟨_, ⟨v, rfl⟩, rfl⟩
      exact ⟨θ v, by simp [T, hθ]⟩
    · rintro ⟨X, rfl⟩
      obtain ⟨v, rfl⟩ := θ.surjective X
      exact ⟨_, ⟨v, rfl⟩, by simp [T, hθ]⟩
  have h1 : Module.finrank (ZMod 2) (LinearMap.range (a.toLinearMap - LinearMap.id)) =
      Module.finrank (ZMod 2) (LinearMap.range T) := by
    rw [← θ.finrank_map_eq, hmap]
    rfl
  rw [h1, ← Module.finrank_mul_finrank (ZMod 2) K (LinearMap.range T), Nat.mul_comm]
  exact Nat.mul_le_mul_left _ (two_le_finrank_range_omega h4 hg hne)

end Module

end P5

end G11

end CFSG.Quasithin
