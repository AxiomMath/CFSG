module

public import CFSG.RankThree.PartOne.AUTSL.OmegaFamily
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public noncomputable section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open Subgroup
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.OrthogonalTail
open scoped Pointwise

variable {K : Type} [Field K]

abbrev omegaTailV (K : Type) [Field K] : Type :=
  (Fin (4 - 1) ⊕ Fin (4 - 1) → K) × (Fin 2 → K)

noncomputable abbrev omegaTailQ (K : Type) [Field K] (b c : K) : QuadraticForm K (omegaTailV K) :=
  quadTail (4 - 1) (minusTailForm K b c)

noncomputable abbrev omegaTailE (K : Type) [Field K] (b c : K) :
    Subgroup (omegaTailV K ≃ₗ[K] omegaTailV K) :=
  orthElementaryGroup (omegaTailQ K b c)

abbrev omegaTailFlag (i : Fin (4 - 1)) : Submodule K (omegaTailV K) :=
  tailFlag K (Fin 2 → K) (4 - 1) (i + 1)

noncomputable abbrev omegaTailBorel (K : Type) [Field K] (b c : K) :
    Subgroup (omegaTailV K ≃ₗ[K] omegaTailV K) :=
  tailBorel (4 - 1) (minusTailForm K b c)

noncomputable abbrev omegaTailParabolic (K : Type) [Field K] (b c : K) (i : Fin (4 - 1)) :
    Subgroup ↥(omegaTailE K b c) :=
  (MulAction.stabilizer (omegaTailV K ≃ₗ[K] omegaTailV K) (omegaTailFlag (K := K) i)).subgroupOf
    (omegaTailE K b c)

noncomputable abbrev omegaTailN (K : Type) [Field K] (b c : K) (a₀ : Fin 2 → K)
    (i : Fin (4 - 1)) : ↥(omegaTailE K b c) :=
  ⟨tailWeylElt (4 - 1) (minusTailForm K b c) a₀ i,
    tailWeylElt_mem (qA := minusTailForm K b c) a₀ i⟩

theorem omegaTail_anisotropic (b c : K) (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    (minusTailForm K b c).Anisotropic :=
  anisotropic_minusTailForm hirr

theorem omegaTail_weylElt_mem_parabolic (b c : K) (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    (a₀ : Fin 2 → K) (ha₀ : a₀ ≠ 0) (i j : Fin (4 - 1)) :
    omegaTailN (K := K) b c a₀ j ∈ omegaTailParabolic (K := K) b c i ↔ j ≠ i := by
  rw [omegaTailParabolic, Subgroup.mem_subgroupOf, omegaTailN, omegaTailFlag,
    MulAction.mem_stabilizer_iff]
  exact tailWeylElt_smul_tailFlag (qA := minusTailForm K b c)
    (omegaTail_anisotropic b c hirr) ha₀ i j

theorem omegaTail_overgroup_eq_iInf (b c : K) (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    (a₀ : Fin 2 → K) (ha₀ : a₀ ≠ 0) (M : Subgroup ↥(omegaTailE K b c))
    (hBM : (omegaTailBorel K b c).subgroupOf (omegaTailE K b c) ≤ M) :
    M = ⨅ i ∈ {i : Fin (4 - 1) | omegaTailN (K := K) b c a₀ i ∉ M},
      omegaTailParabolic (K := K) b c i := by
  classical
  set J : Set (Fin (4 - 1)) := {i : Fin (4 - 1) | omegaTailN (K := K) b c a₀ i ∉ M} with hJ
  have hMG : M.map (omegaTailE K b c).subtype ≤ omegaTailE K b c := Subgroup.map_subtype_le M
  have hBMa : omegaTailBorel K b c ≤ M.map (omegaTailE K b c).subtype := by
    intro x hx
    exact ⟨⟨x, tailBorel_le hx⟩, hBM (Subgroup.mem_subgroupOf.mpr hx), rfl⟩
  have hkey := tail_overgroup_stabilizers (qA := minusTailForm K b c)
    (omegaTail_anisotropic b c hirr) ha₀ hMG hBMa
  have hJeq : {i : Fin (4 - 1) | tailWeylElt (4 - 1) (minusTailForm K b c) a₀ i ∉
      M.map (omegaTailE K b c).subtype} = J := by
    ext i
    simp only [hJ, Set.mem_setOf_eq, omegaTailN]
    exact (Subgroup.mem_map_iff_mem (f := (omegaTailE K b c).subtype)
      (omegaTailE K b c).subtype_injective (x := omegaTailN (K := K) b c a₀ i)).not
  rw [hJeq] at hkey
  have hsub : M = ((omegaTailE K b c) ⊓ ⨅ i ∈ J, MulAction.stabilizer
      (omegaTailV K ≃ₗ[K] omegaTailV K) (omegaTailFlag (K := K) i)).subgroupOf
      (omegaTailE K b c) := by
    rw [← map_subtype_subgroupOf_eq M, hkey]
  rw [hsub]
  ext x
  simp only [Subgroup.mem_subgroupOf, Subgroup.mem_inf, Subgroup.mem_iInf, omegaTailParabolic]
  constructor
  · rintro ⟨-, h⟩ i hi
    exact h i hi
  · intro h
    exact ⟨x.2, fun i hi => h i hi⟩

end CFSG.LocalAnalysis.UniquenessCase.UC22
