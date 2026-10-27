module

public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434F42Enum

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF81.F4

section CenCard

variable {G : Type*} [Group G]

theorem card_cen_aut (α : MulAut G) (x : G) :
    Nat.card (Subgroup.centralizer ({α x} : Set G)) =
      Nat.card (Subgroup.centralizer ({x} : Set G)) := by
  apply Nat.card_congr
  refine ⟨fun z => ⟨α.symm z.1, ?_⟩, fun z => ⟨α z.1, ?_⟩, fun z => ?_, fun z => ?_⟩
  · have := Subgroup.mem_centralizer_singleton_iff.1 z.2
    rw [Subgroup.mem_centralizer_singleton_iff]
    apply α.injective
    rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
    exact this
  · have := Subgroup.mem_centralizer_singleton_iff.1 z.2
    rw [Subgroup.mem_centralizer_singleton_iff, ← map_mul, ← map_mul, this]
  · exact Subtype.ext (by simp)
  · exact Subtype.ext (by simp)

theorem card_cen_isConj {a b : G} (h : IsConj a b) :
    Nat.card (Subgroup.centralizer ({a} : Set G)) =
      Nat.card (Subgroup.centralizer ({b} : Set G)) := by
  obtain ⟨c, hc⟩ := isConj_iff.1 h
  rw [← hc]
  exact (card_cen_aut (MulAut.conj c) a).symm

end CenCard

end CFSG.RankThree.PartTwo.Sec21.FF81.F4
