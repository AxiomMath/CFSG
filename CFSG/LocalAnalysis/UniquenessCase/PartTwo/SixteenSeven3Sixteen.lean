module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenResults
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenResults2
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenThirteenA
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven3SixteenCase
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenDefs3

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

theorem s16c167_exists_central_z (D : Data G) {V₀ V : Subgroup G} (h : Hyp125 D V₀ V) :
    ∃ z ∈ V ⊓ centralizer (D.T : Set G), z ≠ 1 := by
  have hP := h.pairFacts
  have hVT : V ≤ D.T := s15_13A_le_T h
  have hT2 : IsPGroup 2 D.T := D.sylowM.isPGroup
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Group.IsNilpotent ↥D.T := hT2.isNilpotent
  have hTn : D.T ≤ normalizer (V : Set G) := D.sylowM.le.trans hP.le_normalizer
  have hnormal : (V.subgroupOf D.T).Normal := Subgroup.normal_subgroupOf_of_le_normalizer hTn
  have hne : V.subgroupOf D.T ≠ ⊥ := by
    intro h0
    apply hP.ne_bot
    rw [← Subgroup.map_subgroupOf_eq_of_le hVT, h0, Subgroup.map_bot]
  obtain ⟨⟨y, hy⟩, hy1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp
    (Group.IsNilpotent.inf_center_ne_bot_of_normal hne)
  have hyC : (y : G) ∈ centralizer (D.T : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro t ht
    exact congrArg Subtype.val (Subgroup.mem_center_iff.mp hy.2 ⟨t, ht⟩)
  exact ⟨(y : G), Subgroup.mem_inf.2 ⟨hy.1, hyC⟩, fun h1 => hy1 (Subtype.ext (Subtype.ext h1))⟩

theorem s16c167_centralizer_cClos_le (D : Data G) {V : Subgroup G} (hVT : V ≤ D.T) {z : G}
    (hz : z ∈ V ⊓ centralizer (D.T : Set G)) (i : ℕ) :
    centralizer (E3.cClos V i D.T : Set G) ≤ centralizer ({z} : Set G) := by
  refine Subgroup.centralizer_le ?_
  intro x hx
  rw [Set.mem_singleton_iff] at hx
  rw [hx]
  refine Subgroup.mem_inf.2 ⟨hVT hz.1, ?_⟩
  rw [Subgroup.mem_centralizer_iff]
  intro w hw
  exact Subgroup.mem_centralizer_iff.1 hz.2 w (E3.wClos_le i D.T hw)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
