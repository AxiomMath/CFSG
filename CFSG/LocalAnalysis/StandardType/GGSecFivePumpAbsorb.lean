module

public import CFSG.Assembly.Defs
public import CFSG.LocalAnalysis.StandardType.GGSecFiveIdentDefs
import CFSG.Assembly.Subnormal
import CFSG.LocalAnalysis.StandardType.GGNbrBalanceBasic
import CFSG.LocalAnalysis.StandardType.GGSecFiveRankOneConj
import Mathlib.Tactic.Group

public section

namespace CFSG.StandardType

open CFSG.Assembly

open scoped commutatorElement

private theorem ggOTwoPrime_subgroupOf_normal {G : Type} [Group G] [Finite G] (Y : Subgroup G) :
    ((ggOTwoPrime Y).subgroupOf Y).Normal := by
  rw [Subgroup.normal_subgroupOf_iff (ggOTwoPrime_le Y)]
  intro h g hh hg
  have hY : Y.map (MulAut.conj g).toMonoidHom = Y :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (Subgroup.le_normalizer hg)
  have hmem := Subgroup.mem_map_of_mem (MulAut.conj g).toMonoidHom hh
  rw [ggOTwoPrime_map_conj, hY] at hmem
  simpa only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] using hmem

theorem ggRankOneIn_le_of_isSubnormal {G : Type} [Group G] [Finite G]
    {Bs K N Y Z : Subgroup G} {r : MulAut ↥Bs} (hK : IsComponentOf K Y)
    (hY : Subgroup.centralizer (ggHyperplane Bs r : Set G) ≤ Y)
    (hq : CFSG.Assembly.IsQuasisimple ↥(ggRankOneIn K Bs r)) (hN : IsSubnormal N Z)
    (hZ : Subgroup.centralizer (ggHyperplane Bs r : Set G) ≤ Z) {n u : G}
    (hn : n ∈ ggRankOneIn K Bs r) (hu : u ∈ N)
    (huC : u ∈ Subgroup.centralizer (ggHyperplane Bs r : Set G)) (hnu : n * u ≠ u * n) :
    ggRankOneIn K Bs r ≤ N := by
  set H := Subgroup.centralizer (ggHyperplane Bs r : Set G)
  have hSle : ggRankOneIn K Bs r ≤ K ⊓ H := ggOTwoPrime_le _
  have hKH : IsSubnormal (K ⊓ H) H := by
    have h := hK.2.1.inf H
    rwa [inf_eq_right.mpr hY] at h
  have hS : IsComponentOf (ggRankOneIn K Bs r) H :=
    ⟨hSle.trans inf_le_right,
      IsSubnormal.step hSle (ggOTwoPrime_subgroupOf_normal (K ⊓ H)) hKH, hq⟩
  have hNH : IsSubnormal (N ⊓ H) H := by
    have h := hN.inf H
    rwa [inf_eq_right.mpr hZ] at h
  rcases isComponentOf_le_or_commutator_eq_bot hS hNH with h | h
  · exact h.trans inf_le_left
  · exfalso
    apply hnu
    have hmem : ⁅n, u⁆ ∈ ⁅ggRankOneIn K Bs r, N ⊓ H⁆ :=
      Subgroup.commutator_mem_commutator hn (Subgroup.mem_inf.mpr ⟨hu, huC⟩)
    rw [h, Subgroup.mem_bot, commutatorElement_def] at hmem
    calc n * u = n * u * n⁻¹ * u⁻¹ * (u * n) := by group
      _ = u * n := by rw [hmem, one_mul]

end CFSG.StandardType

end
