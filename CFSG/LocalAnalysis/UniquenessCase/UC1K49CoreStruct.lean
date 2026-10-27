module

public import CFSG.LocalAnalysis.UniquenessCase.UC1K49CoreStructCase
public import CFSG.LocalAnalysis.UniquenessCase.UC1K49CoreStructFive
public import CFSG.LocalAnalysis.UniquenessCase.UC1K49CoreStructTwoA
public import CFSG.LocalAnalysis.UniquenessCase.UC1K49CoreStructTwoB
public import CFSG.LocalAnalysis.UniquenessCase.UC1K49CoreStructOne
public import CFSG.LocalAnalysis.UniquenessCase.UC1K49CoreStructPack

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.InS3.UC49

variable {G : Type} [Group G] [Finite G]

open scoped commutatorElement IsMulCommutative
open CFSG.ABGLocalTools

section Context

variable {H X L Q I : Subgroup G} {x : G} {A : Subgroup G} {a n : G} {N M : Subgroup G}
variable (c : Ctx49 H X L Q I x A a n N M)
variable [hNorm : (M.subgroupOf N).Normal] [hElem : IsElementaryAbelian 2 (N ⧸ M.subgroupOf N)]

include c in
theorem chief_struct49_not_IIa : ¬ PatIIa (c.opA 0) (c.opA 1) (c.opA 2) := by
  intro hP
  have hW := c.wt
  have hle := hW.finrank_fixed_le_four (c.disj (Or.inl hP))
  obtain ⟨w, hw, hw0⟩ := hW.exists_ne_zero_Wbz2
  obtain ⟨-, -, h20, h21, h22⟩ := hP
  have hmem : w ∈ LinearMap.range (e2 (c.opA 0)) :=
    (mem_range_e2_iff (c.opA 0) hW.cube0 w).mpr (h20 w hw)
  have h8 := c.five_rank_two ⟨w, hmem, fun h => hw0 (h21 w hw h)⟩
    ⟨w, hmem, fun h => hw0 (h22 w hw h)⟩
  omega

include c in
theorem chief_struct49_not_IIb : ¬ PatIIb (c.opA 0) (c.opA 1) (c.opA 2) := by
  intro hP
  have hle := c.wt.finrank_le_eight hP (c.disj (Or.inr hP))
  have h12 := c.twelve_le
  omega

include c in
theorem chief_struct49_of_caseI (hP : PatI (c.opA 0) (c.opA 1) (c.opA 2)) :
    ChiefShape49 H L Q x N M := by
  intro V hV
  have h3 := c.caseI_L_trivial hP V hV
  have h1 := chief_struct49_sup_eq c.setup c.hx c.xa c.chief c.nontriv V hV
  have h2 := c.direct V hV h3
  exact ⟨h1, h2, h3, c.irred V hV h1 h2 h3⟩

end Context

theorem chief_struct49 {H X L Q I : Subgroup G} (h : Setup49 H X L Q I) {x : G}
    (hx : X = Subgroup.zpowers x) {A : Subgroup G} {a n : G} (hd : XAData X L I x A a n)
    (hFive : FiveRankBound) {N M : Subgroup G} (hch : HChief H N M) (hNQ : N ≤ Q)
    (hI : ¬ ⁅N, I⁆ ≤ M) (hw : wIdx (Z49 X A) N M ≤ 64) :
    ChiefShape49 H L Q x N M := by
  haveI : (M.subgroupOf N).Normal := hch.normal
  haveI : IsElementaryAbelian 2 (N ⧸ M.subgroupOf N) := hch.isElementaryAbelian
  let c : Ctx49 H X L Q I x A a n N M := ⟨h, hx, hd, hch, hNQ, hI, hw⟩
  rcases c.wt.pat with hP | hP | hP
  · exact chief_struct49_of_caseI c hP
  · exact absurd hP (chief_struct49_not_IIa c)
  · exact absurd hP (chief_struct49_not_IIb c)

end CFSG.LocalAnalysis.UniquenessCase.UC22.InS3.UC49
