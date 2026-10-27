module

public import CFSG.RankThree.GF2n.Smith81.S81A5ConjModQ
public import CFSG.RankThree.GF2n.Smith81.S81A5KerRho
public import CFSG.LocalAnalysis.ComponentInitial.LinearFlagElation

public section

namespace CFSG.RankThree.GF2n.Smith81.A5Cube

open Matrix CFSG.LocalAnalysis.ComponentInitial.LinearFlag

variable {K : Type*} [Field K]

private theorem pa1_cube_eq_one_of_sixth_eq_one [CharP K 2] {c : K} (h6 : c ^ 6 = 1) :
    c ^ 3 = 1 := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have hsq : (c ^ 3 - 1) * (c ^ 3 - 1) = 0 := by
    linear_combination h6 + (1 - c ^ 3) * h2
  exact sub_eq_zero.mp (mul_self_eq_zero.mp hsq)

private theorem pa1_rho_toGL_eq_one_iff [CharP K 2] (x : SpecialLinearGroup (Fin 6) K) :
    rho K (SpecialLinearGroup.toGL x) = 1 ↔ x ∈ scalars 6 K := by
  rw [rho_eq_one_iff, mem_scalars]
  constructor
  · rintro ⟨l, hl3, hx⟩
    have hl0 : l ≠ 0 := by
      rintro rfl
      norm_num at hl3
    refine ⟨Units.mk0 l hl0, ?_, ?_⟩
    · ext
      rw [Units.val_pow_eq_pow_val, Units.val_mk0, Units.val_one]
      linear_combination (l ^ 3 + 1) * hl3
    · have hx' : (x : Matrix (Fin 6) (Fin 6) K) = l • (1 : Matrix (Fin 6) (Fin 6) K) := hx
      rw [hx', Units.val_mk0, scalar_apply, smul_one_eq_diagonal]
  · rintro ⟨c, hc6, hx⟩
    have hc6' : (c : K) ^ 6 = 1 := by
      have h := congrArg Units.val hc6
      rwa [Units.val_pow_eq_pow_val, Units.val_one] at h
    refine ⟨(c : K), pa1_cube_eq_one_of_sixth_eq_one hc6', ?_⟩
    change (x : Matrix (Fin 6) (Fin 6) K) = (c : K) • (1 : Matrix (Fin 6) (Fin 6) K)
    rw [hx, scalar_apply, smul_one_eq_diagonal]

theorem rho_eq_iff_proj_eq [CharP K 2] (g h : SpecialLinearGroup (Fin 6) K) :
    rho K (SpecialLinearGroup.toGL g) = rho K (SpecialLinearGroup.toGL h) ↔ proj 6 K g = proj 6 K h := by
  have hone : rho K 1 = 1 := map_one (TauCeti.extPowerRep K 6 3)
  have hL : ∀ x : SpecialLinearGroup (Fin 6) K,
      rho K (SpecialLinearGroup.toGL x⁻¹) * rho K (SpecialLinearGroup.toGL x) = 1 := by
    intro x
    rw [← rho_mul, ← map_mul SpecialLinearGroup.toGL, inv_mul_cancel,
      map_one SpecialLinearGroup.toGL, hone]
  have hR : ∀ x : SpecialLinearGroup (Fin 6) K,
      rho K (SpecialLinearGroup.toGL x) * rho K (SpecialLinearGroup.toGL x⁻¹) = 1 := by
    intro x
    rw [← rho_mul, ← map_mul SpecialLinearGroup.toGL, mul_inv_cancel,
      map_one SpecialLinearGroup.toGL, hone]
  have hmul : rho K (SpecialLinearGroup.toGL (g⁻¹ * h)) =
      rho K (SpecialLinearGroup.toGL g⁻¹) * rho K (SpecialLinearGroup.toGL h) := by
    rw [map_mul SpecialLinearGroup.toGL, rho_mul]
  rw [proj_eq_proj_iff, ← pa1_rho_toGL_eq_one_iff, hmul]
  constructor
  · intro e
    rw [← e]
    exact hL g
  · intro e
    calc rho K (SpecialLinearGroup.toGL g)
        = rho K (SpecialLinearGroup.toGL g) *
            (rho K (SpecialLinearGroup.toGL g⁻¹) * rho K (SpecialLinearGroup.toGL h)) := by
          rw [e, mul_one]
      _ = (rho K (SpecialLinearGroup.toGL g) * rho K (SpecialLinearGroup.toGL g⁻¹)) *
            rho K (SpecialLinearGroup.toGL h) := by
          rw [mul_assoc]
      _ = rho K (SpecialLinearGroup.toGL h) := by
          rw [hR g, one_mul]

theorem exists_sl_twist {T : Cube K ≃ₗ[K] Cube K} (hT : NormalizesSL T) (g : SpecialLinearGroup (Fin 6) K) :
    ∃ g' : SpecialLinearGroup (Fin 6) K,
      ∀ ξ, T (rho K (SpecialLinearGroup.toGL g) ξ) = rho K (SpecialLinearGroup.toGL g') (T ξ) := by
  obtain ⟨g', hg'det, hg'⟩ := hT (SpecialLinearGroup.toGL g) g.2
  refine ⟨⟨(g' : Matrix (Fin 6) (Fin 6) K), hg'det⟩, fun ξ => ?_⟩
  have hE : SpecialLinearGroup.toGL
      (⟨(g' : Matrix (Fin 6) (Fin 6) K), hg'det⟩ : SpecialLinearGroup (Fin 6) K) = g' :=
    Units.ext rfl
  rw [hE]
  exact hg' ξ

theorem proj_eq_of_twist [CharP K 2] {T : Cube K ≃ₗ[K] Cube K} {g g₁ g₂ : SpecialLinearGroup (Fin 6) K}
    (h₁ : ∀ ξ, T (rho K (SpecialLinearGroup.toGL g) ξ) = rho K (SpecialLinearGroup.toGL g₁) (T ξ))
    (h₂ : ∀ ξ, T (rho K (SpecialLinearGroup.toGL g) ξ) = rho K (SpecialLinearGroup.toGL g₂) (T ξ)) :
    proj 6 K g₁ = proj 6 K g₂ :=
  (rho_eq_iff_proj_eq g₁ g₂).mp (rho_eq_of_twist h₁ h₂).symm

theorem exists_aut_of_normalizes [Finite K] [CharP K 2] {T : Cube K ≃ₗ[K] Cube K} (hT : NormalizesSL T) :
    ∃ α : MulAut (projectiveSL 6 K), ∀ g g' : SpecialLinearGroup (Fin 6) K,
      (∀ ξ, T (rho K (SpecialLinearGroup.toGL g) ξ) = rho K (SpecialLinearGroup.toGL g') (T ξ)) →
        α (proj 6 K g) = proj 6 K g' := by
  choose a ha using exists_sl_twist hT
  have hone : rho K (SpecialLinearGroup.toGL (1 : SpecialLinearGroup (Fin 6) K)) = 1 :=
    (congrArg (rho K) (map_one SpecialLinearGroup.toGL)).trans
      (map_one (TauCeti.extPowerRep K 6 3))
  have hmul : ∀ g h : SpecialLinearGroup (Fin 6) K,
      proj 6 K (a (g * h)) = proj 6 K (a g) * proj 6 K (a h) := by
    intro g h
    rw [← map_mul (proj 6 K) (a g) (a h)]
    refine proj_eq_of_twist (ha (g * h)) ?_
    intro ξ
    have e1 : SpecialLinearGroup.toGL (g * h) =
        SpecialLinearGroup.toGL g * SpecialLinearGroup.toGL h := map_mul _ _ _
    have e2 : SpecialLinearGroup.toGL (a g * a h) =
        SpecialLinearGroup.toGL (a g) * SpecialLinearGroup.toGL (a h) := map_mul _ _ _
    rw [e1, e2, rho_mul, rho_mul, Module.End.mul_apply, Module.End.mul_apply, ha g, ha h]
  obtain ⟨φ, hφ⟩ : ∃ φ : SpecialLinearGroup (Fin 6) K →* projectiveSL 6 K,
      ∀ g, φ g = proj 6 K (a g) :=
    ⟨MonoidHom.mk' (fun g => proj 6 K (a g)) hmul, fun g => rfl⟩
  have hker : scalars 6 K ≤ φ.ker := by
    intro g hg
    rw [MonoidHom.mem_ker, hφ]
    have hpg : proj 6 K g = 1 := proj_eq_one_iff.mpr hg
    have hgl : rho K (SpecialLinearGroup.toGL g) = rho K (SpecialLinearGroup.toGL 1) :=
      (rho_eq_iff_proj_eq g 1).mpr (hpg.trans (map_one (proj 6 K)).symm)
    have h2 : ∀ ξ, T (rho K (SpecialLinearGroup.toGL g) ξ) =
        rho K (SpecialLinearGroup.toGL 1) (T ξ) := by
      intro ξ
      simp only [hgl, hone, Module.End.one_apply]
    rw [proj_eq_of_twist (ha g) h2, map_one]
  obtain ⟨α₀, hα₀⟩ : ∃ α₀ : projectiveSL 6 K →* projectiveSL 6 K,
      ∀ g, α₀ (proj 6 K g) = proj 6 K (a g) :=
    ⟨QuotientGroup.lift (scalars 6 K) φ hker, fun g =>
      (show QuotientGroup.lift (scalars 6 K) φ hker (proj 6 K g) = φ g from rfl).trans (hφ g)⟩
  have hinj : Function.Injective α₀ := by
    rw [injective_iff_map_eq_one]
    intro x hx
    obtain ⟨g, rfl⟩ := proj_surjective 6 K x
    rw [hα₀ g] at hx
    have hρa : rho K (SpecialLinearGroup.toGL (a g)) = 1 :=
      ((rho_eq_iff_proj_eq (a g) 1).mpr (hx.trans (map_one (proj 6 K)).symm)).trans hone
    have hTg : ∀ ξ, T (rho K (SpecialLinearGroup.toGL g) ξ) = T ξ := by
      intro ξ
      rw [ha g ξ, hρa, Module.End.one_apply]
    have hρg : rho K (SpecialLinearGroup.toGL g) = rho K (SpecialLinearGroup.toGL 1) := by
      rw [hone]
      refine LinearMap.ext fun ξ => ?_
      rw [Module.End.one_apply]
      exact T.injective (hTg ξ)
    rw [(rho_eq_iff_proj_eq g 1).mp hρg, map_one]
  have hfin : Finite (projectiveSL 6 K) := Finite.of_surjective (proj 6 K) (proj_surjective 6 K)
  have hbij : Function.Bijective α₀ := Finite.injective_iff_bijective.mp hinj
  refine ⟨MulEquiv.ofBijective α₀ hbij, fun g g' hgg' => ?_⟩
  show α₀ (proj 6 K g) = proj 6 K g'
  rw [hα₀ g]
  exact proj_eq_of_twist (ha g) hgg'

end CFSG.RankThree.GF2n.Smith81.A5Cube
