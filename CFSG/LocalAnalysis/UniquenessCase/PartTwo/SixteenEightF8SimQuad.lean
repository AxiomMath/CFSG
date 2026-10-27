module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightF8SimMult

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open Matrix CFSG.RankThree.GF2n.Stroth80

private noncomputable def s16g_sqEquiv (K : Type) [Field K] [Finite K] [CharP K 2] : K ≃ K :=
  Equiv.ofBijective (fun x : K => x ^ 2)
    ⟨CharTwo.sq_injective, Finite.injective_iff_surjective.1 CharTwo.sq_injective⟩

private theorem s16g_polar_eq_of_quad_eq {ι : Type} [Fintype ι] [DecidableEq ι]
    {K : Type} [Field K] {Q : QuadraticForm K (ι → K)} {A : Matrix ι ι K}
    (h : ∀ v, Q (A *ᵥ v) = Q v) :
    ∀ x y, QuadraticMap.polar Q (A *ᵥ x) (A *ᵥ y) = QuadraticMap.polar Q x y := by
  intro x y
  rw [QuadraticMap.polar, QuadraticMap.polar, ← Matrix.mulVec_add, h, h, h]

private theorem s16g_toBilin_smul_of_transpose_mul_eq {ι : Type} [Fintype ι] [DecidableEq ι]
    {K : Type} [Field K] {B : Matrix ι ι K} {g : Matrix ι ι K} {c : K}
    (h : gᵀ * B * g = c • B) (x y : ι → K) :
    B.toBilin' (g *ᵥ x) (g *ᵥ y) = c * B.toBilin' x y := by
  have h1 : B.toBilin'.comp (Matrix.toLin' g) (Matrix.toLin' g) = (gᵀ * B * g).toBilin' :=
    Matrix.toBilin'_comp B g g
  have h2 : B.toBilin' (g *ᵥ x) (g *ᵥ y) = (gᵀ * B * g).toBilin' x y := by
    rw [← h1]
    rfl
  rw [h2, h, Matrix.toBilin'_apply', Matrix.toBilin'_apply', Matrix.smul_mulVec,
    dotProduct_smul, smul_eq_mul]

private theorem s16g_transpose_mul_eq_of_toBilin_eq {ι : Type} [Fintype ι] [DecidableEq ι]
    {K : Type} [Field K] {B : Matrix ι ι K} {g : Matrix ι ι K}
    (h : ∀ x y, B.toBilin' (g *ᵥ x) (g *ᵥ y) = B.toBilin' x y) :
    gᵀ * B * g = B := by
  apply Matrix.toBilin'.injective
  rw [← Matrix.toBilin'_comp B g g]
  refine LinearMap.ext₂ fun x y => ?_
  rw [LinearMap.BilinForm.comp_apply, Matrix.toLin'_apply, Matrix.toLin'_apply]
  exact h x y

private theorem s16g_quad_eq_of_polar_smul {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    {K : Type} [Field K] [Finite K] [CharP K 2] (Q : QuadraticForm K (ι → K))
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) {Γ : Subgroup (GL ι K)}
    (hΓ : AddCommutantScalar Γ) (hΓQ : ∀ A ∈ Γ, ∀ v, Q ((A : Matrix ι ι K) *ᵥ v) = Q v)
    {g : GL ι K} (hg : g ∈ Subgroup.normalizer (Γ : Set (GL ι K))) {c : K}
    (hc : ∀ x y, QuadraticMap.polar Q ((g : Matrix ι ι K) *ᵥ x) ((g : Matrix ι ι K) *ᵥ y) =
      c * QuadraticMap.polar Q x y) :
    ∀ v, Q ((g : Matrix ι ι K) *ᵥ v) = c * Q v := by
  let P : LinearMap.BilinForm K (ι → K) := QuadraticMap.polarBilin Q
  have hP : P = QuadraticMap.polarBilin Q := rfl
  have hPapp : ∀ x y, P x y = QuadraticMap.polar Q x y := by
    intro x y
    rw [hP, QuadraticMap.polarBilin_apply_apply]
  let D : (ι → K) → K := fun x => Q ((g : Matrix ι ι K) *ᵥ x) - c * Q x
  have hDadd : ∀ x y, D (x + y) = D x + D y := by
    intro x y
    have h1 : Q ((g : Matrix ι ι K) *ᵥ (x + y)) =
        Q ((g : Matrix ι ι K) *ᵥ x) + Q ((g : Matrix ι ι K) *ᵥ y) +
          c * QuadraticMap.polar Q x y := by
      rw [Matrix.mulVec_add, QuadraticMap.map_add Q ((g : Matrix ι ι K) *ᵥ x)
        ((g : Matrix ι ι K) *ᵥ y), hc]
    have h2 : Q (x + y) = Q x + Q y + QuadraticMap.polar Q x y :=
      QuadraticMap.map_add Q x y
    change Q ((g : Matrix ι ι K) *ᵥ (x + y)) - c * Q (x + y) =
      (Q ((g : Matrix ι ι K) *ᵥ x) - c * Q x) +
        (Q ((g : Matrix ι ι K) *ᵥ y) - c * Q y)
    rw [h1, h2]
    ring
  have hDsmul : ∀ (a : K) (x : ι → K), D (a • x) = a * a * D x := by
    intro a x
    have h1 : Q ((g : Matrix ι ι K) *ᵥ (a • x)) =
        a * a * Q ((g : Matrix ι ι K) *ᵥ x) := by
      rw [Matrix.mulVec_smul, QuadraticMap.map_smul, smul_eq_mul]
    have h2 : Q (a • x) = a * a * Q x := by
      rw [QuadraticMap.map_smul, smul_eq_mul]
    change Q ((g : Matrix ι ι K) *ᵥ (a • x)) - c * Q (a • x) =
      a * a * (Q ((g : Matrix ι ι K) *ᵥ x) - c * Q x)
    rw [h1, h2]
    ring
  have hDinv : ∀ A ∈ Γ, ∀ x, D (A *ᵥ x) = D x := by
    intro A hA x
    have hA' : g * A * g⁻¹ ∈ Γ := (Subgroup.mem_normalizer_iff.1 hg A).1 hA
    have he : (g : Matrix ι ι K) * (A : Matrix ι ι K) =
        ((g * A * g⁻¹ : GL ι K) : Matrix ι ι K) * (g : Matrix ι ι K) := by
      rw [← Units.val_mul, ← Units.val_mul]
      congr 1
      simp only [mul_assoc, inv_mul_cancel, mul_one]
    have h1 : Q ((g : Matrix ι ι K) *ᵥ ((A : Matrix ι ι K) *ᵥ x)) =
        Q ((g : Matrix ι ι K) *ᵥ x) := by
      rw [Matrix.mulVec_mulVec, he, ← Matrix.mulVec_mulVec, hΓQ _ hA' _]
    have h2 : Q ((A : Matrix ι ι K) *ᵥ x) = Q x := hΓQ A hA x
    change Q ((g : Matrix ι ι K) *ᵥ ((A : Matrix ι ι K) *ᵥ x)) -
        c * Q ((A : Matrix ι ι K) *ᵥ x) =
      Q ((g : Matrix ι ι K) *ᵥ x) - c * Q x
    rw [h1, h2]
  let r : K → K := (s16g_sqEquiv K).symm
  have hr : ∀ a : K, (r a) ^ 2 = a := fun a => Equiv.apply_symm_apply (s16g_sqEquiv K) a
  let ℓfun : (ι → K) → K := fun x => r (D x)
  have hℓadd : ∀ x y, ℓfun (x + y) = ℓfun x + ℓfun y := by
    intro x y
    rw [← CharTwo.sq_inj]
    change (r (D (x + y))) ^ 2 = (r (D x) + r (D y)) ^ 2
    rw [hr, hDadd, CharTwo.add_sq, hr, hr]
  have hℓsmul : ∀ (a : K) (x : ι → K), ℓfun (a • x) = a * ℓfun x := by
    intro a x
    rw [← CharTwo.sq_inj]
    change (r (D (a • x))) ^ 2 = (a * r (D x)) ^ 2
    rw [hr, hDsmul, mul_pow, hr]
    ring
  let ℓ : (ι → K) →ₗ[K] K :=
    { toFun := ℓfun
      map_add' := hℓadd
      map_smul' := fun a x => by simpa [smul_eq_mul] using hℓsmul a x }
  have hℓinv : ∀ A ∈ Γ, ∀ x, ℓfun (A *ᵥ x) = ℓfun x := by
    intro A hA x
    rw [← CharTwo.sq_inj]
    change (r (D (A *ᵥ x))) ^ 2 = (r (D x)) ^ 2
    rw [hr, hr, hDinv A hA x]
  obtain ⟨z, hz⟩ : ∃ z : ι → K, ∀ x, P z x = ℓfun x := by
    refine ⟨(P.toDual hQ).symm ℓ, fun x => ?_⟩
    exact LinearMap.BilinForm.apply_toDual_symm_apply ℓ x
  have hzfix : ∀ A ∈ Γ, (A : Matrix ι ι K) *ᵥ z = z := by
    intro A hA
    have hsep : ∀ y : ι → K, P ((A : Matrix ι ι K) *ᵥ z - z) y = 0 := by
      intro y
      obtain ⟨x, rfl⟩ : ∃ x : ι → K, (A : Matrix ι ι K) *ᵥ x = y := by
        refine ⟨((A⁻¹ : GL ι K) : Matrix ι ι K) *ᵥ y, ?_⟩
        rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one,
          Matrix.one_mulVec]
      have hiso : P ((A : Matrix ι ι K) *ᵥ z) ((A : Matrix ι ι K) *ᵥ x) = P z x := by
        rw [hPapp, hPapp]
        exact s16g_polar_eq_of_quad_eq (hΓQ A hA) z x
      have hzx : P z ((A : Matrix ι ι K) *ᵥ x) = P z x := by
        rw [hz ((A : Matrix ι ι K) *ᵥ x), hz x, hℓinv A hA x]
      rw [LinearMap.map_sub, LinearMap.sub_apply, hiso, hzx, sub_self]
    exact sub_eq_zero.1 (hQ.1 ((A : Matrix ι ι K) *ᵥ z - z) hsep)
  let f : (ι → K) →+ (ι → K) :=
    { toFun := fun x => P z x • z
      map_zero' := by simp
      map_add' := fun x y => by rw [LinearMap.map_add, add_smul] }
  have hcomm : ∀ A ∈ Γ, ∀ v, f (A *ᵥ v) = (A : Matrix ι ι K) *ᵥ f v := by
    intro A hA v
    have hzv : P z ((A : Matrix ι ι K) *ᵥ v) = P z v := by
      rw [hz ((A : Matrix ι ι K) *ᵥ v), hz v, hℓinv A hA v]
    change P z ((A : Matrix ι ι K) *ᵥ v) • z =
      (A : Matrix ι ι K) *ᵥ (P z v • z)
    rw [hzv, Matrix.mulVec_smul, hzfix A hA]
  obtain ⟨e, he⟩ := hΓ f hcomm
  have hPzz : P z z = 0 := by
    rw [hPapp, QuadraticMap.polar_self, two_smul, CharTwo.add_self_eq_zero]
  have hz0 : z = 0 := by
    by_contra hzne
    have hez : e • z = 0 := by
      have hfz : f z = P z z • z := rfl
      rw [← he z, hfz, hPzz, zero_smul]
    have he0 : e = 0 := by
      rcases smul_eq_zero.1 hez with h | h
      · exact h
      · exact absurd h hzne
    have hf0 : ∀ v, P z v = 0 := by
      intro v
      have hv : P z v • z = 0 := by
        have hfv : f v = P z v • z := rfl
        rw [← hfv, he v, he0, zero_smul]
      rcases smul_eq_zero.1 hv with h | h
      · exact h
      · exact absurd h hzne
    exact hzne (hQ.1 z hf0)
  have hℓ0 : ∀ v, r (D v) = 0 := by
    intro v
    change ℓfun v = 0
    rw [← hz v, hz0]
    simp
  intro v
  have hDv : D v = 0 := by
    have h := hr (D v)
    rw [hℓ0 v] at h
    simpa using h.symm
  exact sub_eq_zero.1 hDv

theorem s16g_exists_mult_quadratic {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    {K : Type} [Field K] [Finite K] [CharP K 2] (Q : QuadraticForm K (ι → K))
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) {Γ : Subgroup (GL ι K)}
    (hΓ : AddCommutantScalar Γ) (hΓQ : ∀ A ∈ Γ, ∀ v, Q ((A : Matrix ι ι K) *ᵥ v) = Q v) :
    ∃ μ : ↥(Subgroup.normalizer (Γ : Set (GL ι K))) →* Kˣ,
      (∀ (g : ↥(Subgroup.normalizer (Γ : Set (GL ι K)))) (v : ι → K),
        Q (((g : GL ι K) : Matrix ι ι K) *ᵥ v) = (μ g : K) * Q v) ∧
      ∀ g : ↥(Subgroup.normalizer (Γ : Set (GL ι K))),
        μ g = 1 ↔ ∀ v : ι → K, Q (((g : GL ι K) : Matrix ι ι K) *ᵥ v) = Q v := by
  let B : Matrix ι ι K := LinearMap.BilinForm.toMatrix' (QuadraticMap.polarBilin Q)
  have hBilin : Matrix.toBilin' B = QuadraticMap.polarBilin Q :=
    Matrix.toBilin'_toMatrix' _
  have hBnd : B.Nondegenerate := by
    rw [← Matrix.nondegenerate_toBilin'_iff]
    rw [hBilin]
    exact hQ
  have hBdet : IsUnit B.det := by
    rw [isUnit_iff_ne_zero]
    exact (Matrix.nondegenerate_iff_det_ne_zero).1 hBnd
  have hΓB : ∀ A ∈ Γ, (A : Matrix ι ι K)ᵀ * B * (A : Matrix ι ι K) = B := by
    intro A hA
    apply s16g_transpose_mul_eq_of_toBilin_eq
    intro x y
    simp only [hBilin, QuadraticMap.polarBilin_apply_apply]
    exact s16g_polar_eq_of_quad_eq (hΓQ A hA) x y
  obtain ⟨μ, hμ, hμ1⟩ := s16g_exists_mult hΓ hBdet hΓB
  have hquad : ∀ (g : ↥(Subgroup.normalizer (Γ : Set (GL ι K)))) (v : ι → K),
      Q (((g : GL ι K) : Matrix ι ι K) *ᵥ v) = (μ g : K) * Q v := by
    intro g v
    refine s16g_quad_eq_of_polar_smul Q hQ hΓ hΓQ (g := (g : GL ι K))
      (c := (μ g : K)) g.2 (fun x y => ?_) v
    have h := s16g_toBilin_smul_of_transpose_mul_eq (B := B)
      (g := ((g : GL ι K) : Matrix ι ι K)) (c := (μ g : K)) (hμ g) x y
    rwa [hBilin, QuadraticMap.polarBilin_apply_apply, QuadraticMap.polarBilin_apply_apply] at h
  refine ⟨μ, hquad, fun g => ⟨?_, ?_⟩⟩
  · intro h1 v
    rw [hquad g v, h1, Units.val_one, one_mul]
  · intro h2
    rw [hμ1 g]
    apply s16g_transpose_mul_eq_of_toBilin_eq
    intro x y
    simp only [hBilin, QuadraticMap.polarBilin_apply_apply]
    exact s16g_polar_eq_of_quad_eq h2 x y

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
