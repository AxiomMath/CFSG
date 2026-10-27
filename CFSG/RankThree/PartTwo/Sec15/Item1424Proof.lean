module

public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.GroupTheory.Fitting.CharacteristicP
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.RankThree.LocalRank.PrimeComplementCentralizesNormal
public import CFSG.RankThree.PartTwo.KFacts.KS18A7M22
public import CFSG.RankThree.PartTwo.Sec13.Item13Models
public import CFSG.RankThree.PartTwo.Sec14.Notation

public section

namespace CFSG.RankThree.PartTwo.Sec15

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec14 CFSG.GH74.GLS
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem inf_centralizer_le_pCoreOf_of_fitting {Y : Subgroup G}
    (hF : generalizedFitting ↥Y = CFSG.pCore 2 ↥Y) :
    Y ⊓ Subgroup.centralizer (CFSG.Open.pCoreOf 2 Y : Set G) ≤ CFSG.Open.pCoreOf 2 Y := by
  rintro y ⟨hyY, hyC⟩
  have h1 : (⟨y, hyY⟩ : Y) ∈ Subgroup.centralizer (generalizedFitting ↥Y : Set ↥Y) := by
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    rw [hF] at hz
    have hz' : (z : G) ∈ CFSG.Open.pCoreOf 2 Y := ⟨z, by assumption, rfl⟩
    exact Subtype.ext (Subgroup.mem_centralizer_iff.mp hyC _ hz')
  have h2 := centralizer_generalizedFitting_le ↥Y h1
  rw [hF] at h2
  exact ⟨⟨y, hyY⟩, by assumption, rfl⟩

omit [Finite G] in
theorem le_normalizer_commutator_of_le {A H K : Subgroup G}
    (hH : A ≤ Subgroup.normalizer (H : Set G)) (hK : A ≤ Subgroup.normalizer (K : Set G)) :
    A ≤ Subgroup.normalizer ((⁅H, K⁆ : Subgroup G) : Set G) := by
  intro x hx
  rw [Subgroup.mem_normalizer_iff_map_conj_eq, Subgroup.map_commutator,
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (hH hx),
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (hK hx)]

end CFSG.RankThree.PartTwo.Sec15
