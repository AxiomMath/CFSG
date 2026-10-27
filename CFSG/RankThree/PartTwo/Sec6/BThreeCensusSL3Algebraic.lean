module

public import CFSG.RankThree.PartOne.KC.LinearSubfieldDescent
public import CFSG.RankThree.PartTwo.Sec6.BThreeCensusSL3
import CFSG.LocalAnalysis.SeitzReduction.E6PilotFieldNormalizePSL
import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.KS.E8FiveTwoUni

public section

namespace CFSG.RankThree.PartTwo.Sec6.BThreeCensus

open CFSG.LocalAnalysis.ComponentInitial.LinearFlag CFSG.RankThree.PartOne Matrix
open CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.KSE8Five.Two

theorem linearSubfieldInclusion_conjAut {Ω : Type} [Field Ω] (E : Subfield Ω)
    (A : GL (Fin 3) E) (g : projectiveSL 3 E) :
    linearSubfieldInclusion 3 E (conjAut 3 E A g) =
      conjAut 3 Ω (GeneralLinearGroup.map E.subtype A) (linearSubfieldInclusion 3 E g) := by
  obtain ⟨B, rfl⟩ := proj_surjective 3 E g
  simp only [conjAut_proj, linearSubfieldInclusion_proj,
    CFSG.SeitzReduction.E6Pilot.map_slConjugation]

theorem isSolvable_of_projective_cube_scalar_over_algebraic
    {K Ω G : Type} [Field K] [Finite K] [Field Ω] [Algebra K Ω]
    [Algebra.IsAlgebraic K Ω] [Group G] [Finite G]
    (h3 : (3 : Ω) ≠ 0) (ρ : G →* projectiveSL 3 Ω)
    (hker : ρ.ker ≤ Subgroup.center G) {A : GL (Fin 3) Ω} {c : Ω}
    (hA3 : (A : Matrix (Fin 3) (Fin 3) Ω) ^ 3 = c • 1)
    (hns : ∀ a : Ω, (A : Matrix (Fin 3) (Fin 3) Ω) ≠ a • 1)
    (hfix : ∀ g : G, conjAut 3 Ω A (ρ g) = ρ g)
    (hNPC : CFSG.HasNormalPComplement 3 ↥(_root_.commutator G)) :
    Group.IsSolvable G := by
  classical
  let entries (M : GL (Fin 3) Ω) : Finset Ω := Finset.univ.biUnion fun i : Fin 3 =>
    Finset.univ.image fun j : Fin 3 => (M : Matrix (Fin 3) (Fin 3) Ω) i j
  have hentry : ∀ M i j, (M : Matrix (Fin 3) (Fin 3) Ω) i j ∈ entries M := by
    intro M i j
    simp only [entries, Finset.mem_biUnion, Finset.mem_univ, Finset.mem_image, true_and]
    exact ⟨i, j, rfl⟩
  let S := insert c (entries A ∪ entries A⁻¹)
  obtain ⟨E, hE, hSE, _, _, _, ρE, hρE, hkerE⟩ :=
    exists_finite_subfield_projectiveSL_lift (by decide) (K := K) ρ S
  let : Finite E := hE
  have hAE : ∀ i j, (A : Matrix (Fin 3) (Fin 3) Ω) i j ∈ E := fun i j =>
    hSE (Finset.mem_insert_of_mem (Finset.mem_union_left _ (hentry A i j)))
  have hAiE : ∀ i j, ((A⁻¹ : GL (Fin 3) Ω) : Matrix (Fin 3) (Fin 3) Ω) i j ∈ E := fun i j =>
    hSE (Finset.mem_insert_of_mem (Finset.mem_union_right _ (hentry A⁻¹ i j)))
  obtain ⟨AE, hAE⟩ := exists_gl_of_entries E A hAE hAiE
  change GeneralLinearGroup.map E.subtype AE = A at hAE
  have hmat : (AE : Matrix (Fin 3) (Fin 3) E).map E.subtype =
      (A : Matrix (Fin 3) (Fin 3) Ω) := congrArg (fun M : GL (Fin 3) Ω =>
        (M : Matrix (Fin 3) (Fin 3) Ω)) hAE
  let cE : E := ⟨c, hSE (Finset.mem_insert_self _ _)⟩
  have hMInj : Function.Injective (fun M : Matrix (Fin 3) (Fin 3) E => M.map E.subtype) := by
    intro M N h
    apply Matrix.ext
    intro i j
    exact E.subtype.injective (congrFun (congrFun h i) j)
  have hA3E : (AE : Matrix (Fin 3) (Fin 3) E) ^ 3 = cE • 1 := by
    apply hMInj
    change ((AE : Matrix (Fin 3) (Fin 3) E) ^ 3).map E.subtype =
      (cE • (1 : Matrix (Fin 3) (Fin 3) E)).map E.subtype
    rw [Matrix.map_pow, hmat, hA3]
    ext i j
    by_cases hij : i = j
    · subst hij; simp [cE]
    · simp [Matrix.one_apply_ne hij]
  have hnsE : ∀ a : E, (AE : Matrix (Fin 3) (Fin 3) E) ≠ a • 1 := by
    intro a ha
    apply hns (a : Ω)
    rw [← hmat, ha]
    ext i j
    by_cases hij : i = j
    · subst hij; simp
    · simp [Matrix.one_apply_ne hij]
  have h3E : (3 : E) ≠ 0 := by
    intro h
    apply h3
    have h' := congrArg E.subtype h
    simpa only [map_ofNat, map_zero] using h'
  have hfixE : ∀ g : G, conjAut 3 E AE (ρE g) = ρE g := by
    intro g
    apply linearSubfieldInclusion_injective (by decide) E
    have hg : linearSubfieldInclusion 3 E (ρE g) = ρ g := DFunLike.congr_fun hρE g
    rw [linearSubfieldInclusion_conjAut, hAE, hg, hfix g]
  exact CFSG.RankThree.PartTwo.Sec6.BThreeCensus.isSolvable_of_projective_cube_scalar_centralizer_and_complement
      h3E ρE (hkerE.le.trans hker) hA3E hnsE hfixE hNPC

end CFSG.RankThree.PartTwo.Sec6.BThreeCensus
