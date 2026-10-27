module

public import CFSG.Quasithin.Background.P3OrthoOm4
public import CFSG.Fischer.F4

public section

namespace CFSG.Quasithin.H13.L1442

open CFSG.Fischer CFSG.Assembly.LowTwoRank Matrix
open CFSG.ComponentClassification.CatalogueBOrthogonalFourSplit

noncomputable abbrev gf4 : GaloisField 2 2 ≃+* F4 := F4.equivGaloisField.symm

theorem four_le_card_gf : 4 ≤ Nat.card (GaloisField 2 2) := by
  rw [GaloisField.card 2 2 (by norm_num)]
  norm_num

theorem rho'_apply_eq (z : SpecialLinearGroup (Fin 2) (GaloisField 2 2) ×
    SpecialLinearGroup (Fin 2) (GaloisField 2 2)) (X : Matrix (Fin 2) (Fin 2) (GaloisField 2 2)) :
    G11.P3Ortho.Om4.rho' (GaloisField 2 2) z X =
      (z.1 : Matrix (Fin 2) (Fin 2) (GaloisField 2 2)) * X *
        ((z.2⁻¹ : SpecialLinearGroup (Fin 2) (GaloisField 2 2)) :
          Matrix (Fin 2) (Fin 2) (GaloisField 2 2)) :=
  specialRho_apply z X

theorem gf4_mul_mul (A X B : Matrix (Fin 2) (Fin 2) (GaloisField 2 2)) :
    gf4.mapMatrix (A * X * B) = gf4.mapMatrix A * gf4.mapMatrix X * gf4.mapMatrix B := by
  rw [map_mul, map_mul]

theorem exists_theta {V : Type} [AddCommGroup V] [Module (ZMod 2) V]
    {K : Subgroup (V ≃ₗ[ZMod 2] V)}
    (hK : G11.IsNaturalMatrixModule K (StatedOmega (StatedQuadPlus 2 (GaloisField 2 2)))) :
    ∃ Θ : V ≃+ Matrix (Fin 2) (Fin 2) F4,
      (∀ γ ∈ K, ∃ A B : SpecialLinearGroup (Fin 2) F4, ∀ v,
        Θ (γ v) = (A : Matrix (Fin 2) (Fin 2) F4) * Θ v * (B : Matrix (Fin 2) (Fin 2) F4)) ∧
      ∀ A B : SpecialLinearGroup (Fin 2) F4, ∃ γ ∈ K, ∀ v,
        Θ (γ v) = (A : Matrix (Fin 2) (Fin 2) F4) * Θ v * (B : Matrix (Fin 2) (Fin 2) F4) := by
  obtain ⟨φ, ψ, hψ⟩ := hK
  have hrange : (StatedOmega (StatedQuadPlus 2 (GaloisField 2 2))).map
      (G11.P3Ortho.Om4.Ψ (GaloisField 2 2)).toMonoidHom =
        (G11.P3Ortho.Om4.rho' (GaloisField 2 2)).range := by
    rw [G11.P3Ortho.Om4.map_statedOmega, G11.P3Ortho.Om4.commutator_eq_range four_le_card_gf]
  let Θ₀ : V ≃+ Matrix (Fin 2) (Fin 2) (GaloisField 2 2) :=
    ψ.toAddEquiv.trans (G11.P3Ortho.Om4.toMat (GaloisField 2 2)).toAddEquiv
  have hΘ₀ : ∀ v, Θ₀ v = G11.P3Ortho.Om4.toMat (GaloisField 2 2) (ψ v) := fun _ => rfl
  have hact : ∀ (γ : ↥K) (v : V), Θ₀ ((γ : V ≃ₗ[ZMod 2] V) v) =
      G11.P3Ortho.Om4.Ψ (GaloisField 2 2) (φ γ) (Θ₀ v) := by
    intro γ v
    rw [hΘ₀, hΘ₀, hψ γ v, G11.P3Ortho.Om4.Ψ_apply, LinearEquiv.symm_apply_apply]
  refine ⟨Θ₀.trans gf4.mapMatrix.toAddEquiv, fun γ hγ => ?_, fun A B => ?_⟩
  · obtain ⟨z, hz⟩ : G11.P3Ortho.Om4.Ψ (GaloisField 2 2) (φ ⟨γ, hγ⟩) ∈
        (G11.P3Ortho.Om4.rho' (GaloisField 2 2)).range :=
      hrange ▸ ⟨_, (φ ⟨γ, hγ⟩).2, rfl⟩
    refine ⟨SpecialLinearGroup.map gf4.toRingHom z.1,
      SpecialLinearGroup.map gf4.toRingHom z.2⁻¹, fun v => ?_⟩
    have h1 := hact ⟨γ, hγ⟩ v
    rw [← hz, rho'_apply_eq] at h1
    show gf4.mapMatrix (Θ₀ (γ v)) = _
    rw [h1, gf4_mul_mul]
    rfl
  · let z : SpecialLinearGroup (Fin 2) (GaloisField 2 2) ×
        SpecialLinearGroup (Fin 2) (GaloisField 2 2) :=
      (SpecialLinearGroup.map gf4.symm.toRingHom A, (SpecialLinearGroup.map gf4.symm.toRingHom B)⁻¹)
    obtain ⟨ω, hω, hωz⟩ : G11.P3Ortho.Om4.rho' (GaloisField 2 2) z ∈
        (StatedOmega (StatedQuadPlus 2 (GaloisField 2 2))).map
          (G11.P3Ortho.Om4.Ψ (GaloisField 2 2)).toMonoidHom := hrange ▸ ⟨z, rfl⟩
    refine ⟨(φ.symm ⟨ω, hω⟩ : V ≃ₗ[ZMod 2] V), (φ.symm ⟨ω, hω⟩).2, fun v => ?_⟩
    have h1 : Θ₀ ((φ.symm ⟨ω, hω⟩ : V ≃ₗ[ZMod 2] V) v) =
        G11.P3Ortho.Om4.Ψ (GaloisField 2 2) ω (Θ₀ v) := by
      have := hact (φ.symm ⟨ω, hω⟩) v
      rwa [MulEquiv.apply_symm_apply] at this
    have h2 : G11.P3Ortho.Om4.Ψ (GaloisField 2 2) ω = G11.P3Ortho.Om4.rho' (GaloisField 2 2) z :=
      hωz
    rw [h2, rho'_apply_eq, inv_inv] at h1
    show gf4.mapMatrix (Θ₀ _) = _
    rw [h1, gf4_mul_mul]
    have hA : gf4.mapMatrix ((SpecialLinearGroup.map gf4.symm.toRingHom A :
        SpecialLinearGroup (Fin 2) (GaloisField 2 2)) : Matrix (Fin 2) (Fin 2) (GaloisField 2 2)) =
        (A : Matrix (Fin 2) (Fin 2) F4) := by
      ext i j
      simp
    have hB : gf4.mapMatrix ((SpecialLinearGroup.map gf4.symm.toRingHom B :
        SpecialLinearGroup (Fin 2) (GaloisField 2 2)) : Matrix (Fin 2) (Fin 2) (GaloisField 2 2)) =
        (B : Matrix (Fin 2) (Fin 2) F4) := by
      ext i j
      simp
    rw [hA, hB]
    rfl

end CFSG.Quasithin.H13.L1442
