module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KRankOneBorel.Dich
public import CFSG.Milestones.ASVolI.A2
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X7aResidual
import CFSG.Milestones.ASVolI.A2OddAut

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.RankOneBorel

open Subgroup Matrix CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.Blueprint (LieModel)

theorem projStabilizer_inf_le_normalizer {K : Type} [Field K] [Finite K] [CharP K 2] :
    projStabilizer (flagSpace 3 K 1) ⊓ projStabilizer (flagSpace 3 K 2) ≤
      normalizer ((projUnitriangular 3 K : Subgroup (projectiveSL 3 K)) :
        Set (projectiveSL 3 K)) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro x hx
  rw [normalizer_projUnitriangular (K := K) (n := 3) 2]
  obtain ⟨hx1, hx2⟩ := Subgroup.mem_inf.mp hx
  obtain ⟨g, hg1, rfl⟩ := Subgroup.mem_map.mp hx1
  obtain ⟨g', hg2, hg'⟩ := Subgroup.mem_map.mp hx2
  have hsc : g⁻¹ * g' ∈ scalars 3 K := proj_eq_proj_iff.mp hg'.symm
  have hg2' : g ∈ stabilizer (flagSpace 3 K 2) := by
    have h1 : g⁻¹ * g' ∈ stabilizer (flagSpace 3 K 2) := scalars_le_stabilizer _ hsc
    have heq : g = g' * (g⁻¹ * g')⁻¹ := by group
    rw [heq]
    exact (stabilizer (flagSpace 3 K 2)).mul_mem hg2 ((stabilizer (flagSpace 3 K 2)).inv_mem h1)
  refine Subgroup.mem_map.mpr ⟨g, ?_, rfl⟩
  rw [CFSG.QuasithinUnique.Setup.X7a.upperTriangular_eq_flagStabilizer]
  exact mem_flagStabilizer.mpr fun i hi => by
    rcases (show i = 1 ∨ i = 2 from by simpa using hi) with rfl | rfl
    · exact hg1
    · exact hg2'

theorem exists_eq_conjAut_mul_fieldAut_of_map_eq {K : Type} [Field K] [Finite K]
    (α : MulAut (projectiveSL 3 K))
    (hα : (projStabilizer (flagSpace 3 K 1)).map α.toMonoidHom =
      projStabilizer (flagSpace 3 K 1)) :
    ∃ (A : GL (Fin 3) K) (σ : K ≃+* K), α = conjAut 3 K A * fieldAut 3 K σ := by
  refine type_preserving_automorphisms (by norm_num : 3 ≤ 3) α fun L hL => ?_
  have hF1 : Module.finrank K (flagSpace 3 K 1) = 1 := finrank_flagSpace (by norm_num)
  obtain ⟨g, hg⟩ := exists_map_eq_of_finrank_eq (W := flagSpace 3 K 1) (W' := L)
    (by rw [hF1, hL])
  obtain ⟨g'', hg''⟩ := proj_surjective 3 K (α (proj 3 K g))
  refine ⟨(flagSpace 3 K 1).map (mulVecLin (g'' : Matrix (Fin 3) (Fin 3) K)), ?_, ?_⟩
  · exact (LinearEquiv.finrank_map_eq (Matrix.SpecialLinearGroup.toLin' g'')
      (flagSpace 3 K 1)).trans hF1
  ·
    have hPL : projStabilizer L =
        (projStabilizer (flagSpace 3 K 1)).map (MulAut.conj (proj 3 K g)) := by
      rw [← hg, projStabilizer_map_conj]
    rw [hPL, CFSG.LocalAnalysis.ComponentInitial.LinearFlag.map_map_conj]
    have hα' : Subgroup.map (↑α : projectiveSL 3 K →* projectiveSL 3 K)
        (projStabilizer (flagSpace 3 K 1)) = projStabilizer (flagSpace 3 K 1) := hα
    rw [hα', ← hg'']
    exact projStabilizer_map_conj g'' (flagSpace 3 K 1)

theorem isInnDiagFieldAut_of_congr_eq {X : Type} [Group X] {K : Type} [Field K] [Finite K]
    {n : ℕ} (hK : Nat.card K = 2 ^ n) (φ : X ≃* projectiveSL 3 K) (θ : MulAut X)
    (A : GL (Fin 3) K) (σ : K ≃+* K) (h : MulAut.congr φ θ = conjAut 3 K A * fieldAut 3 K σ) :
    CFSG.ASVolI.ChA.IsInnDiagFieldAut X θ := by
  set Ψ : CFSG.Open.StatedProj (CFSG.Open.StatedSL 3 K) ≃* projectiveSL 3 K :=
    CFSG.ASVolI.burnsideA26_statedToProjSL 3 K with hΨ
  set e : X ≃* CFSG.Open.StatedProj (CFSG.Open.StatedSL 3 K) := φ.trans Ψ.symm with he
  have heφ : e.trans Ψ = φ := by
    rw [he]
    ext x
    simp
  have hθ : θ = MulAut.congr φ.symm (conjAut 3 K A) *
      MulAut.congr φ.symm (fieldAut 3 K σ) := by
    rw [← map_mul, ← h, CFSG.ASVolI.burnsideA26_congr_symm_congr]
  refine ⟨MulAut.congr φ.symm (conjAut 3 K A), MulAut.congr φ.symm (fieldAut 3 K σ),
    ?_, ?_, hθ⟩
  · refine Or.inr (Or.inl ⟨n, K, inferInstance, inferInstance, e, A, hK, ?_⟩)
    rw [show MulAut.congr e (MulAut.congr φ.symm (conjAut 3 K A)) =
      MulAut.congr e (MulAut.congr (e.trans Ψ).symm (conjAut 3 K A)) by rw [heφ]]
    exact CFSG.ASVolI.burnsideA26_isProjConjAut e A
  · refine Or.inr (Or.inl ⟨n, K, inferInstance, inferInstance, e, σ, hK, ?_⟩)
    rw [show MulAut.congr e (MulAut.congr φ.symm (fieldAut 3 K σ)) =
      MulAut.congr e (MulAut.congr (e.trans Ψ).symm (fieldAut 3 K σ)) by rw [heφ]]
    exact CFSG.ASVolI.burnsideA26_isProjFieldAut e σ

theorem graphL3_dich {X : Type} [Group X] [Finite X] {n : ℕ} (hX : LieModel X .PSL 3 2 n)
    (θ : MulAut X) (hθ : ¬ CFSG.ASVolI.ChA.IsInnDiagFieldAut X θ) (S : Sylow 2 X)
    (hθS : (S : Subgroup X).map θ.toMonoidHom = S) (H : Subgroup X)
    (hSH : (S : Subgroup X) ≤ H) (hθH : H.map θ.toMonoidHom = H) :
    H ≤ normalizer ((S : Subgroup X) : Set X) ∨ H = ⊤ := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hU : CFSG.QuasithinUnique.IsSylowTwoOf (S : Subgroup X) ⊤ :=
    CFSG.QuasithinUnique.isSylowTwoOf_top_of_sylow S
  obtain ⟨K, _, _, _, φ, hK, hφU, hR, -⟩ :=
    CFSG.QuasithinUnique.Setup.X7a.even_rank_two_residual_linear
      (CFSG.Blueprint.LieModel.statedClassicalModel_of_ne_zero (by norm_num) hX) hU
  have hS : Subgroup.map φ.symm.toMonoidHom (projUnitriangular 3 K) = (S : Subgroup X) := by
    rw [← hφU, Subgroup.map_map]
    simp
  let P : Fin 2 → Subgroup X := fun j =>
    Subgroup.map φ.symm.toMonoidHom (projStabilizer (flagSpace 3 K ((j : ℕ) + 1)))
  have hinf : P 0 ⊓ P 1 ≤ normalizer ((S : Subgroup X) : Set X) := by
    have h0 : P 0 = Subgroup.map φ.symm.toMonoidHom
        (projStabilizer (flagSpace 3 K 1)) := rfl
    have h1 : P 1 = Subgroup.map φ.symm.toMonoidHom
        (projStabilizer (flagSpace 3 K 2)) := rfl
    rw [h0, h1, ← Subgroup.map_inf (projStabilizer (flagSpace 3 K 1))
      (projStabilizer (flagSpace 3 K 2)) φ.symm.toMonoidHom φ.symm.injective]
    calc Subgroup.map φ.symm.toMonoidHom
          (projStabilizer (flagSpace 3 K 1) ⊓ projStabilizer (flagSpace 3 K 2))
        ≤ Subgroup.map φ.symm.toMonoidHom (normalizer ((projUnitriangular 3 K :
            Subgroup (projectiveSL 3 K)) : Set (projectiveSL 3 K))) :=
          Subgroup.map_mono projStabilizer_inf_le_normalizer
      _ = normalizer ((Subgroup.map φ.symm.toMonoidHom (projUnitriangular 3 K) :
            Subgroup X) : Set X) := Subgroup.map_equiv_normalizer_eq _ φ.symm
      _ = normalizer ((S : Subgroup X) : Set X) := by rw [hS]
  have hθP : Subgroup.map θ.toMonoidHom (P 0) ≠ P 0 := by
    have h0 : P 0 = Subgroup.map φ.symm.toMonoidHom
        (projStabilizer (flagSpace 3 K 1)) := rfl
    rw [h0]
    intro heq
    apply hθ
    have hcomp : φ.toMonoidHom.comp (θ.toMonoidHom.comp φ.symm.toMonoidHom) =
        (MulAut.congr φ θ).toMonoidHom := by
      ext x
      simp [MulAut.congr_apply]
    have h := congrArg (Subgroup.map φ.toMonoidHom) heq
    simp only [Subgroup.map_map, MonoidHom.comp_assoc] at h
    rw [hcomp] at h
    have hα : Subgroup.map (MulAut.congr φ θ).toMonoidHom
        (projStabilizer (flagSpace 3 K 1)) = projStabilizer (flagSpace 3 K 1) := by
      simpa using h
    obtain ⟨A, σ, hAσ⟩ := exists_eq_conjAut_mul_fieldAut_of_map_eq (MulAut.congr φ θ) hα
    exact isInnDiagFieldAut_of_congr_eq hK φ θ A σ hAσ
  exact dich_of_residual hR hinf θ hθS hθP H hSH hθH

end CFSG.LocalAnalysis.UniquenessCase.UC22.RankOneBorel
