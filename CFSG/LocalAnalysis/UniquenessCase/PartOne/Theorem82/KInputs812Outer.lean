module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.KInputs812
import CFSG.GroupTheory.CyclicSylowThreeSplit
import CFSG.LocalAnalysis.ComponentClassification.OuterAutomorphisms
import CFSG.LocalAnalysis.UniquenessCase.UC1K31
import CFSG.GroupTheory.ABGLocalTools.CoreLemmas

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82

open CFSG.ComponentClassification.OuterAutomorphisms

theorem outerThreeSplit_holds : OuterThreeSplit := by
  rintro X _ _ _ hXq _ hrank R S hR hS hSR α hα hα3
  classical
  haveI : Fact (Nat.Prime 3) := ⟨by decide⟩
  have hInorm : (inner X).Normal := inner_normal X
  have hXperf : ⁅(⊤ : Subgroup X), ⊤⁆ = ⊤ := hXq.1
  have hIperf : ⁅inner X, inner X⁆ = inner X := by
    have h := Subgroup.map_commutator (⊤ : Subgroup X) ⊤ (MulAut.conj : X →* MulAut X)
    rw [Subgroup.map_top, hXperf, Subgroup.map_top] at h
    exact h.symm
  obtain ⟨Q⟩ := (inferInstance : Nonempty (Sylow 3 X))
  have hQcyc : IsCyclic ↥(Q : Subgroup X) := by
    refine CFSG.LocalAnalysis.UniquenessCase.UCK.K31.isCyclic_of_pRank_le_one
      (p := 3) (by decide) (by decide) Q.isPGroup' ?_
    have h := CFSG.SectionRank.pRank_mono (p := 3) (by norm_num)
      (le_top : (Q : Subgroup X) ≤ ⊤)
    rwa [hrank] at h
  let π : X →* ↥(inner X) :=
    (MulAut.conj : X →* MulAut X).codRestrict (inner X) fun x => ⟨x, rfl⟩
  have hπ : Function.Surjective π := by
    rintro ⟨y, hy⟩
    obtain ⟨x, rfl⟩ := hy
    exact ⟨x, rfl⟩
  have hcomp : (inner X).subtype.comp π = (MulAut.conj : X →* MulAut X) := rfl
  let P' : Subgroup (MulAut X) := Subgroup.map (MulAut.conj : X →* MulAut X) (Q : Subgroup X)
  have hP'syl : CFSG.ABGLocalTools.IsSylowOf 3 P' (inner X) := by
    refine ⟨Sylow.mapSurjective (f := π) hπ Q, ?_⟩
    rw [Sylow.coe_mapSurjective, Subgroup.map_map, hcomp]
  have hP'cyc : IsCyclic ↥P' := by
    haveI := hQcyc
    let f : ↥(Q : Subgroup X) →* ↥P' :=
      ((MulAut.conj : X →* MulAut X).comp (Q : Subgroup X).subtype).codRestrict P'
        fun x => Subgroup.mem_map.mpr ⟨x.1, x.2, rfl⟩
    refine isCyclic_of_surjective f ?_
    intro y
    obtain ⟨s, hs, hsy⟩ := Subgroup.mem_map.mp y.2
    exact ⟨⟨s, hs⟩, Subtype.ext hsy⟩
  have hScyc : IsCyclic ↥S := by
    obtain ⟨k, _, hconj⟩ := hP'syl.exists_mem_conj hS
    have hSeq : S = Subgroup.map (MulAut.conj k) P' := by
      ext x
      rw [Subgroup.mem_map]
      constructor
      · intro hx
        exact ⟨k⁻¹ * x * k, (hconj x).mp hx, by
          show k * (k⁻¹ * x * k) * k⁻¹ = x
          group⟩
      · rintro ⟨y, hy, rfl⟩
        refine (hconj (k * y * k⁻¹)).mpr ?_
        rwa [show k⁻¹ * (k * y * k⁻¹) * k = y from by group]
    rw [hSeq]
    haveI := hP'cyc
    let f : ↥P' →* ↥(Subgroup.map (MulAut.conj k) P') :=
      ((MulAut.conj k).toMonoidHom.comp P'.subtype).codRestrict _
        fun x => Subgroup.mem_map.mpr ⟨x.1, x.2, rfl⟩
    refine isCyclic_of_surjective f ?_
    intro y
    obtain ⟨s, hs, hsy⟩ := Subgroup.mem_map.mp y.2
    exact ⟨⟨s, hs⟩, Subtype.ext hsy⟩
  exact CFSG.GroupTheory.exists_mul_pow_three_eq_one_of_isCyclic hInorm hIperf hR hS hScyc hSR
    hα hα3

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82
