module

public import CFSG.LocalAnalysis.UniquenessCase.UC6S35Core
public import CFSG.LocalAnalysis.UniquenessCase.UC6Defs2
public import CFSG.GroupTheory.SteinbergBKOddNoncyclicRankTwo
public import CFSG.LocalAnalysis.UniquenessCase.UC6K

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC6

open Subgroup CFSG.Open
open CFSG.Yardstones.Mf4cdcdf2e013 (Standing4 Setup4 TheoremCAt Theorem614Four)

namespace Mz614

variable {G : Type} [Group G] [Finite G] (m : Mz614 G)

theorem sylow_cyclic_of_pRank_eq_one (h625 : m.C625) (hodd : Odd m.r) :
    ∀ S : Sylow m.r ↥m.K, IsCyclic ↥S := by
  intro S
  by_contra hnc
  haveI : Fact m.r.Prime := ⟨m.hr⟩
  obtain ⟨B, hBel, hBcard⟩ :=
    CFSG.GroupTheory.SteinbergBK.odd_noncyclic_pgroup_rank_two hodd S.isPGroup' hnc
  set E : Subgroup G := (B.map (S : Subgroup ↥m.K).subtype).map m.K.subtype with hE
  have hE_le : E ≤ m.K := Subgroup.map_subtype_le _
  have hEel : IsElemAbelian m.r E := by
    have h1 : IsElemAbelian m.r B := isElemAbelian_iff_isElementaryAbelian.mpr hBel
    exact (h1.map (S : Subgroup ↥m.K).subtype).map m.K.subtype
  have hEcard : Nat.card E = m.r ^ 2 := by
    rw [hE, Subgroup.card_map_of_injective m.K.subtype_injective,
      Subgroup.card_map_of_injective (S : Subgroup ↥m.K).subtype_injective]
    exact hBcard
  have h2 := le_pRank_of_elemAbelian m.hr hE_le hEel hEcard
  have h1 : CFSG.Open.pRank m.r m.K = 1 := h625
  omega

theorem three_lt_r (h625 : m.C625) (h629 : m.C629) (h634 : m.C634) : 3 < m.r := by
  have hr := m.hr
  have hr2 : m.r ≠ 2 := m.d.odd
  by_contra hle
  have h3 : m.r = 3 := by have := hr.two_le; omega
  have hodd : Odd m.r := hr.odd_of_ne_two hr2
  have hZcard : Nat.card (m.Z.subgroupOf m.K) = m.r := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe m.Z_le_K).toEquiv]; exact m.card_Z
  obtain ⟨t, ht⟩ := exists_inverting_of_cyclic_sylow h3 hZcard h629.1 h629.2
    (m.sylow_cyclic_of_pRank_eq_one h625 hodd)
  apply h634
  refine ⟨(t : G), t.2, fun z hz => ?_⟩
  have := ht ⟨z, m.Z_le_K hz⟩ (by simpa [Subgroup.mem_subgroupOf] using hz)
  exact congrArg Subtype.val this

end Mz614

end CFSG.LocalAnalysis.UniquenessCase.UC6
