module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KAdj.SpBorel
public import CFSG.LocalAnalysis.UniquenessCase.UC22Defs2

import CFSG.LocalAnalysis.ComponentInitial.SymplecticHigherSylow
import CFSG.LocalAnalysis.ComponentInitial.SymplecticHigherBorel
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.ParabolicTransfer
public import CFSG.LocalAnalysis.ComponentInitial.SymplecticFlagOrder

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.KAdjE

open CFSG.Open CFSG.LocalAnalysis.ComponentInitial
open SymplecticFlag (borelSubgroup unipotent)
open SymplecticHigher (flagStabilizer)
open KTabD (lineStab)

theorem unipotent_le_lineStab (m : ℕ) (K : Type) [Field K] :
    unipotent (m + 2) K ≤ lineStab (StatedSp (m + 2) K) (Pi.single (Sum.inl 0) 1) := by
  intro u hu
  rw [lineStab_statedSp_eq_flagStabilizer]
  have huB : u ∈ flagStabilizer (m + 2) K (Set.Icc 2 (m + 2)) ⊓
      flagStabilizer (m + 2) K ({1} : Set ℕ) := by
    rw [flagStabilizer_inf_eq_borelSubgroup]
    exact SymplecticFlag.unipotent_le_borelSubgroup hu
  exact huB.2

theorem unipotent_le_flagStabilizer_alpha (m : ℕ) (K : Type) [Field K] :
    unipotent (m + 2) K ≤ flagStabilizer (m + 2) K (Set.Icc 2 (m + 2)) := by
  intro u hu
  exact SymplecticHigher.borelSubgroup_le_flagStabilizer
    (fun i hi => (Set.mem_Icc.mp hi).2) (SymplecticFlag.unipotent_le_borelSubgroup hu)

theorem isParabolicTwo_flagStabilizer_alpha (m : ℕ) (K : Type) [Field K] [Finite K] [CharP K 2] :
    IsParabolicTwo ↥(StatedSp (m + 2) K) (flagStabilizer (m + 2) K (Set.Icc 2 (m + 2))) := by
  obtain ⟨S, hS⟩ := SymplecticFlag.exists_sylow_unipotent (K := K) 2 (m + 2)
  have hSset : (S : Set (StatedSp (m + 2) K)) =
      (unipotent (m + 2) K : Set (StatedSp (m + 2) K)) := congrArg SetLike.coe hS
  refine ⟨S, ?_⟩
  rw [hSset, SymplecticHigher.normalizer_unipotent]
  exact SymplecticHigher.borelSubgroup_le_flagStabilizer (fun i hi => (Set.mem_Icc.mp hi).2)

theorem not_flagStabilizer_alpha_le_lineStab (m : ℕ) (K : Type) [Field K] :
    ¬ flagStabilizer (m + 2) K (Set.Icc 2 (m + 2)) ≤
      lineStab (StatedSp (m + 2) K) (Pi.single (Sum.inl 0) 1) := by
  intro h
  have hnQ : SymplecticHigher.weylRep K (0 : Fin (m + 2)) ∈
      flagStabilizer (m + 2) K (Set.Icc 2 (m + 2)) := by
    rw [(SymplecticHigher.subflag_generation (Set.Icc 2 (m + 2))
      (fun i hi => (Set.mem_Icc.mp hi).2)).2.1 (0 : Fin (m + 2))]
    simp
  have hnStab := h hnQ
  rw [lineStab_statedSp_eq_flagStabilizer] at hnStab
  have hn1 : ((0 : Fin (m + 2)) : ℕ) + 1 ∈ ({1} : Set ℕ) := by simp
  exact ((SymplecticHigher.subflag_generation ({1} : Set ℕ) (fun i hi => by
    rw [Set.mem_singleton_iff] at hi
    subst hi
    omega)).2.1 (0 : Fin (m + 2))).mp hnStab hn1

theorem flagStabilizer_alpha_le_of_parabolic (m : ℕ) {K : Type} [Field K] [Finite K] [CharP K 2]
    {P : Subgroup ↥(StatedSp (m + 2) K)} (hP : IsParabolicTwo ↥(StatedSp (m + 2) K) P)
    (hU : unipotent (m + 2) K ≤ P)
    (hnot : ¬ P ≤ lineStab (StatedSp (m + 2) K) (Pi.single (Sum.inl 0) 1)) :
    flagStabilizer (m + 2) K (Set.Icc 2 (m + 2)) ≤ P := by
  obtain ⟨S, hS⟩ := SymplecticFlag.exists_sylow_unipotent (K := K) 2 (m + 2)
  have hSset : (S : Set ↥(StatedSp (m + 2) K)) =
      (unipotent (m + 2) K : Set (StatedSp (m + 2) K)) := congrArg SetLike.coe hS
  have hSP : (S : Subgroup ↥(StatedSp (m + 2) K)) ≤ P := by
    intro x hx
    have hx' : x ∈ (unipotent (m + 2) K : Set (StatedSp (m + 2) K)) := by
      rw [← hSset]
      exact hx
    exact hU hx'
  have hB : borelSubgroup (m + 2) K ≤ P := by
    rw [← SymplecticHigher.normalizer_unipotent]
    have h := hP.normalizer_le S hSP
    rwa [hSset] at h
  obtain ⟨hPcut, -⟩ := SymplecticHigher.borel_overgroups (K := K) P hB
  have h1not : 1 ∉ SymplecticHigher.borelCuts K P := by
    intro h1mem
    apply hnot
    rw [hPcut]
    rw [lineStab_statedSp_eq_flagStabilizer]
    intro g hg
    rw [SymplecticHigher.mem_flagStabilizer] at hg
    rw [SymplecticHigher.mem_flagStabilizer]
    intro i hi
    rw [Set.mem_singleton_iff] at hi
    subst hi
    exact hg 1 h1mem
  have hsub : ∀ i ∈ SymplecticHigher.borelCuts K P, i ∈ Set.Icc 2 (m + 2) := by
    intro i hi
    obtain ⟨h1i, h2i⟩ := SymplecticHigher.borelCuts_le P i hi
    have hne : i ≠ 1 := fun he => h1not (he ▸ hi)
    exact Set.mem_Icc.mpr ⟨by omega, h2i⟩
  rw [hPcut]
  intro g hg
  rw [SymplecticHigher.mem_flagStabilizer] at hg
  rw [SymplecticHigher.mem_flagStabilizer]
  intro i hi
  exact hg i (hsub i hi)

end CFSG.LocalAnalysis.UniquenessCase.UC22.KAdjE
