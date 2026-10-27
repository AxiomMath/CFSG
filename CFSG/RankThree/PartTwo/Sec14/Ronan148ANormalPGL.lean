module

public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHeldSmallCoreLinear
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.RankThree.PartTwo.Sec14.Item148StepOne
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.RankThree.PartTwo.Sec14.Ronan148A

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec14
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.LocalRank CFSG.GH74.GLS

variable {G : Type} [Group G] [Finite G]

section Quot

variable {A Y : Subgroup G} [(ker148 A Y).Normal]

theorem alpha148_mem_of_inf_of_le (hA3 : ∀ a ∈ A, a ^ 3 = 1) {J Y' : Subgroup G} (hJY : J ≤ Y')
    (hOY : pPrimeCoreOf 3 Y ≤ Y') {e : G} (he : e ∈ A) (hAe : A ⊓ Y' ≤ Subgroup.zpowers e)
    {b : ↥(Y ⊔ A) ⧸ ker148 A Y} (hbA : b ∈ img148 A Y A) (hbJ : b ∈ img148 A Y J)
    (hb1 : b ≠ 1) : alpha148 A Y e he ∈ img148 A Y J := by
  obtain ⟨a, haM, haA, rfl⟩ := mem_img148_iff.mp hbA
  obtain ⟨g, hgM, hgJ, hga⟩ := mem_img148_iff.mp hbJ
  have hag : a⁻¹ * g ∈ pPrimeCoreOf 3 Y := by
    have := mk'_ker148_eq_iff.mp hga.symm
    simpa using this
  have haY' : a ∈ Y' := by
    have h1 : a⁻¹ * g ∈ Y' := hOY hag
    have h2 : g ∈ Y' := hJY hgJ
    have : a = g * (a⁻¹ * g)⁻¹ := by group
    rw [this]
    exact Y'.mul_mem h2 (Y'.inv_mem h1)
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (hAe ⟨haA, haY'⟩)
  have he3 : alpha148 A Y e he ^ 3 = 1 := alpha148_pow_three hA3 he
  have hbe : QuotientGroup.mk' (ker148 A Y) ⟨a, haM⟩ = alpha148 A Y e he ^ k := by
    rw [alpha148_eq_mk', ← map_zpow]
    congr 1
    exact Subtype.ext (by simp [hk])
  have hord : orderOf (QuotientGroup.mk' (ker148 A Y) ⟨a, haM⟩) = 3 := by
    have h3 : (QuotientGroup.mk' (ker148 A Y) ⟨a, haM⟩) ^ 3 = 1 := by
      rw [← map_pow]
      have : (⟨a, haM⟩ : ↥(Y ⊔ A)) ^ 3 = 1 := Subtype.ext (by simpa using hA3 a haA)
      rw [this, map_one]
    exact orderOf_eq_prime h3 hb1
  have hle : Subgroup.zpowers (QuotientGroup.mk' (ker148 A Y) ⟨a, haM⟩) ≤
      Subgroup.zpowers (alpha148 A Y e he) := by
    rw [Subgroup.zpowers_le, hbe]
    exact Subgroup.zpow_mem_zpowers _ k
  have heq := Subgroup.eq_of_le_of_card_ge hle (by
    rw [Nat.card_zpowers, Nat.card_zpowers, hord]
    exact Nat.le_of_dvd (by norm_num) (orderOf_dvd_of_pow_eq_one he3))
  have hmem : alpha148 A Y e he ∈
      Subgroup.zpowers (QuotientGroup.mk' (ker148 A Y) ⟨a, haM⟩) := by
    rw [heq]
    exact Subgroup.mem_zpowers _
  exact (Subgroup.zpowers_le.mpr hbJ) hmem

end Quot

end CFSG.RankThree.PartTwo.Sec14.Ronan148A
