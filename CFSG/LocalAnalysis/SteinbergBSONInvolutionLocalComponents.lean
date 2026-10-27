module

public import CFSG.Sporadic.Schreier.ONCentralQuotient
public import CFSG.LinearAlgebra.LinearGroups.ProjectiveSimple
public import CFSG.GroupTheory.LocalCores.Components
public import CFSG.LocalAnalysis.ComponentInitial.LocalComponents

public section

namespace CFSG.LocalAnalysis.SteinbergBS

open CFSG CFSG.LocalCores CFSG.ONSchreier

theorem component_eq_of_commutator_le {M : Type*} [Group M] {L : Subgroup M}
    (hL : IsQuasisimple L) (hcomm : commutator M ≤ L) {B : Subgroup M} (hB : IsComponent B) :
    B = L := by
  have hBperf : ⁅B, B⁆ = B := by
    have h := hB.1.1
    rw [Group.isPerfect_def] at h
    rw [← Subgroup.map_subtype_commutator, h, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  have hBL : B ≤ L := by
    rw [← hBperf]
    exact (Subgroup.commutator_mono le_top le_top).trans hcomm
  have hB' := component_overgroup hB hBL
  rcases CFSG.LocalAnalysis.ComponentInitial.quasisimple_subnormal_subgroups hL hB'.2 with
    htop | hle
  · exact le_antisymm hBL (Subgroup.subgroupOf_eq_top.1 htop)
  · exfalso
    obtain ⟨⟨-, -, a, b, hab⟩, -⟩ := hB'
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective a
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective b
    have hxy : x * y = y * x := Subtype.ext (Subgroup.mem_center_iff.1 (hle y.2) x)
    exact hab (by rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, hxy])

theorem onX_isSimpleGroup
    : IsSimpleGroup onX := by
  obtain ⟨θ, -⟩ := at_on_standard_psl34_action.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hs := (CFSG.LinearGroups.linear_projective_simple
    (K := CFSG.ComponentClassification.PSL3Four.F4) (n := 3) (by norm_num)
    (Or.inl le_rfl)).2.1
  exact ((θ.symm.trans (QuotientGroup.quotientMulEquivOfEq
    (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.scalars_eq_center 3
      CFSG.ComponentClassification.PSL3Four.F4)))).isSimpleGroup

theorem onL_isQuasisimple :
    IsQuasisimple onL ∧ Nat.card (onL ⧸ Subgroup.center onL) = 20160 := by
  obtain ⟨-, -, -, -, hperf, -⟩ := at_on_perfect_derived_subgroup
  obtain ⟨e⟩ := at_on_local_central_quotient.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  have hcardX := at_on_standard_psl34_action.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hcard : Nat.card (onL ⧸ Subgroup.center onL) = 20160 := by
    rw [Nat.card_congr e.toEquiv, hcardX]
  have := onX_isSimpleGroup
  have hs : IsSimpleGroup (onL ⧸ Subgroup.center onL) := e.isSimpleGroup
  refine ⟨⟨hperf, hs, ?_⟩, hcard⟩
  by_contra hab
  have : IsMulCommutative (onL ⧸ Subgroup.center onL) :=
    ⟨⟨fun a b => not_not.1 fun h => hab ⟨a, b, h⟩⟩⟩
  have hp := Group.is_simple_iff_prime_card.1 hs
  rw [hcard] at hp
  norm_num at hp

end CFSG.LocalAnalysis.SteinbergBS
