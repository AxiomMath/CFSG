module

public import CFSG.RankThree.PartOne.K159.Klein

public section

namespace CFSG.RankThree.GF2n.Stroth80

open Matrix CFSG.Open CFSG.LocalAnalysis CFSG.LieType.Universal.Spin
open CFSG.RankThree.PartOne.K159

variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem mem_statedOmega_quadPlus_three_iff (A : GL (Fin 3 ⊕ Fin 3) K) :
    A ∈ StatedOmega (StatedQuadPlus 3 K) ↔
      ∃ g : SpecialLinearGroup (Fin 4) K,
        Klein.rho g = CFSG.ClassicalGroups.Orthogonal.toLinEquiv (Fin 3 ⊕ Fin 3) K A := by
  rw [CFSG.ClassicalGroups.Orthogonal.statedOmega_eq_comap (coe_quadPlus 3 K),
    Subgroup.mem_comap]
  obtain ⟨hs, hp⟩ := Klein.sl4_isSimpleGroup_and_perfect (K := K)
  haveI := hs
  haveI := hp
  obtain ⟨-, -, -, -, -, -, hcomm, -⟩ :=
    CFSG.RankThree.PartOne.KCOrthogonal.derived_of_index_two_model
      (TauCeti.QuadraticMap.orthogonalGroup (quadPlus 3 K))
      (Klein.rho : SpecialLinearGroup (Fin 4) K →* _) Klein.rho_injective
      (by rintro _ ⟨g, rfl⟩; exact Klein.rho_mem g) Klein.card_orthogonalGroup_quadPlus_three
  rw [hcomm, MonoidHom.mem_range]
  rfl

theorem exists_sl4_of_omegaPlus_three {H : Type*} [Group H] (φ : H →* GL (Fin 3 ⊕ Fin 3) K)
    (hφ : φ.range = StatedOmega (StatedQuadPlus 3 K)) :
    ∃ η : H →* SpecialLinearGroup (Fin 4) K, Function.Surjective η ∧
      (∀ h, η h = 1 ↔ φ h = 1) ∧ ∀ h (u : Fin 3 ⊕ Fin 3 → K),
        Klein.rho (η h) u = (φ h : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) K) *ᵥ u := by
  classical
  let κ := MonoidHom.ofInjective (Klein.rho_injective (K := K))
  let ψ : H →* ((Fin 3 ⊕ Fin 3 → K) ≃ₗ[K] (Fin 3 ⊕ Fin 3 → K)) :=
    (CFSG.ClassicalGroups.Orthogonal.toLinEquiv (Fin 3 ⊕ Fin 3) K).toMonoidHom.comp φ
  have hψ : ∀ h, ψ h ∈ (Klein.rho : SpecialLinearGroup (Fin 4) K →* _).range := by
    intro h
    have hmem : φ h ∈ StatedOmega (StatedQuadPlus 3 K) := by rw [← hφ]; exact ⟨h, rfl⟩
    obtain ⟨g, hg⟩ := (mem_statedOmega_quadPlus_three_iff (φ h)).mp hmem
    exact ⟨g, hg⟩
  let η : H →* SpecialLinearGroup (Fin 4) K := κ.symm.toMonoidHom.comp (ψ.codRestrict _ hψ)
  have hη : ∀ h, Klein.rho (η h) = ψ h := by
    intro h
    have e := κ.apply_symm_apply ⟨ψ h, hψ h⟩
    exact congrArg Subtype.val e
  refine ⟨η, fun g => ?_, fun h => ?_, fun h u => ?_⟩
  · have hmem : CFSG.ClassicalGroups.Orthogonal.toLinEquiv (Fin 3 ⊕ Fin 3) K
        ((CFSG.ClassicalGroups.Orthogonal.toLinEquiv (Fin 3 ⊕ Fin 3) K).symm (Klein.rho g)) ∈
          (Klein.rho : SpecialLinearGroup (Fin 4) K →* _).range := by
      rw [MulEquiv.apply_symm_apply]
      exact ⟨g, rfl⟩
    have hA : (CFSG.ClassicalGroups.Orthogonal.toLinEquiv (Fin 3 ⊕ Fin 3) K).symm (Klein.rho g) ∈
        StatedOmega (StatedQuadPlus 3 K) := by
      rw [mem_statedOmega_quadPlus_three_iff]
      exact ⟨g, (MulEquiv.apply_symm_apply _ _).symm⟩
    rw [← hφ] at hA
    obtain ⟨h, hh⟩ := hA
    refine ⟨h, Klein.rho_injective ?_⟩
    rw [hη]
    show CFSG.ClassicalGroups.Orthogonal.toLinEquiv (Fin 3 ⊕ Fin 3) K (φ h) = Klein.rho g
    rw [hh, MulEquiv.apply_symm_apply]
  · constructor
    · intro h1
      have h2 : ψ h = 1 := by rw [← hη, h1, map_one]
      exact (CFSG.ClassicalGroups.Orthogonal.toLinEquiv (Fin 3 ⊕ Fin 3) K).injective
        (h2.trans (map_one _).symm)
    · intro h1
      apply Klein.rho_injective
      rw [hη, map_one]
      show CFSG.ClassicalGroups.Orthogonal.toLinEquiv (Fin 3 ⊕ Fin 3) K (φ h) = 1
      rw [h1, map_one]
  · rw [hη]
    rfl

omit [Finite K] in
theorem kleinRho_map {K' : Type} [Field K'] [CharP K' 2] (f : K →+* K')
    (g : SpecialLinearGroup (Fin 4) K) (u : Fin 3 ⊕ Fin 3 → K) :
    Klein.rho (SpecialLinearGroup.map f g) (fun i => f (u i)) = fun i => f (Klein.rho g u i) := by
  rw [Klein.rho_apply, Klein.rho_apply, Klein.cong_apply, Klein.cong_apply]
  have halt : Klein.alt (fun i => f (u i)) = (Klein.alt u).map f := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Klein.alt, antiMat]
  have hmap : (SpecialLinearGroup.map f g : Matrix (Fin 4) (Fin 4) K') =
      (g : Matrix (Fin 4) (Fin 4) K).map f := rfl
  rw [halt, hmap, ← Matrix.transpose_map, ← Matrix.map_mul, ← Matrix.map_mul]
  funext i
  rcases i with i | i <;> fin_cases i <;> simp [Klein.coords]

end CFSG.RankThree.GF2n.Stroth80
