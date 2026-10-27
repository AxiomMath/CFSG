module

public import CFSG.Foundations.Basic
import CFSG.RankThree.PartTwo.Sec18.Components
import CFSG.LieType.SteinbergBRMulEquivCores

public section

namespace CFSG.RankThree.PartTwo.Sec21

open CFSG

namespace Item228Census3Proof

theorem inSubgroup_perfectResidual_eq_of_commutator {G : Type*} [Group G] {C N : Subgroup G}
    (hNC : N ≤ C) (hN : ⁅N, N⁆ = N) (hcomm : ∀ x ∈ C, ∀ y ∈ C, x * y * x⁻¹ * y⁻¹ ∈ N) :
    inSubgroup perfectResidual C = N := by
  apply le_antisymm
  · have h1 : perfectResidual C ≤ derivedSeries C 1 := iInf_le _ 1
    rw [derivedSeries_one] at h1
    calc inSubgroup perfectResidual C = (perfectResidual C).map C.subtype := rfl
      _ ≤ (commutator C).map C.subtype := Subgroup.map_mono h1
      _ = ⁅C, C⁆ := by
          rw [commutator_def, Subgroup.map_commutator, ← MonoidHom.range_eq_map,
            Subgroup.range_subtype]
      _ ≤ N := Subgroup.commutator_le.mpr fun x hx y hy => by
          rw [commutatorElement_def]
          exact hcomm x hx y hy
  · exact Sec18.le_inSubgroup_perfectResidual hN hNC

theorem map_inSubgroup_perfectResidual {G G' : Type*} [Group G] [Group G'] (e : G ≃* G')
    (H : Subgroup G) :
    (inSubgroup perfectResidual H).map e.toMonoidHom =
      inSubgroup perfectResidual (H.map e.toMonoidHom) := by
  set e' : H ≃* H.map e.toMonoidHom := H.equivMapOfInjective e.toMonoidHom e.injective
  have h1 := CFSG.LieType.SteinbergBR.perfectResidual_map_equiv e'
  have h2 : (H.map e.toMonoidHom).subtype.comp e'.toMonoidHom = e.toMonoidHom.comp H.subtype := by
    ext x
    rfl
  rw [inSubgroup, inSubgroup, ← h1, Subgroup.map_map, Subgroup.map_map, h2]

theorem map_centralizer_singleton {G G' : Type*} [Group G] [Group G'] (e : G ≃* G') (z : G) :
    (Subgroup.centralizer ({z} : Set G)).map e.toMonoidHom =
      Subgroup.centralizer ({e z} : Set G') := by
  ext x
  rw [Subgroup.mem_map_equiv, Subgroup.mem_centralizer_singleton_iff,
    Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro h
    have := congrArg e h
    rwa [map_mul, map_mul, MulEquiv.apply_symm_apply] at this
  · intro h
    apply e.injective
    rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
    exact h

noncomputable def perfectResidualCentralizerEquiv {G G' : Type*} [Group G] [Group G'] (e : G ≃* G')
    (z : G) :
    inSubgroup perfectResidual (Subgroup.centralizer ({z} : Set G)) ≃*
      inSubgroup perfectResidual (Subgroup.centralizer ({e z} : Set G')) :=
  ((inSubgroup perfectResidual (Subgroup.centralizer ({z} : Set G))).equivMapOfInjective
    e.toMonoidHom e.injective).trans (MulEquiv.subgroupCongr (by
      rw [map_inSubgroup_perfectResidual, map_centralizer_singleton]))

end Item228Census3Proof

end CFSG.RankThree.PartTwo.Sec21
