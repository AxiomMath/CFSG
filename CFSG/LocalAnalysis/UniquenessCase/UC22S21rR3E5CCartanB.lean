module

public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma54
public import CFSG.LocalAnalysis.AGLEmbedding.SeitzEqTwo.DescentE
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoAltCenter
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Bar13
public import CFSG.LocalAnalysis.UniquenessCase.UC22BarLemmas
public import CFSG.LocalAnalysis.UniquenessCase.UC22S21rR3E5CNorm
public import CFSG.Quasithin.Vol2.Ch10SecKGA318
public import CFSG.RankThree.PartTwo.KFacts.KS21Mult
public import CFSG.RankThree.PartTwo.Sec3.TwoThreeStructure

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.QuasithinUnique (IsSylowTwoOf)
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

private theorem uc22r3e5c_normalizer_subgroupOf {X P : Subgroup G} (hPX : P ≤ X) :
    Subgroup.normalizer ((P.subgroupOf X : Subgroup ↥X) : Set ↥X) =
      (X ⊓ Subgroup.normalizer (P : Set G)).subgroupOf X := by
  ext g
  constructor
  · intro hg
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_inf]
    refine ⟨g.2, ?_⟩
    rw [Subgroup.mem_normalizer_iff]
    intro p
    constructor
    · intro hp
      have h1 : (⟨p, hPX hp⟩ : ↥X) ∈ P.subgroupOf X := Subgroup.mem_subgroupOf.mpr hp
      have h2 := (Subgroup.mem_normalizer_iff.mp hg (⟨p, hPX hp⟩ : ↥X)).mp h1
      exact Subgroup.mem_subgroupOf.mp h2
    · intro hp
      have hpX : p ∈ X := by
        have h1 : (g : G) * p * (g : G)⁻¹ ∈ X := hPX hp
        have h2 := X.mul_mem (X.mul_mem (X.inv_mem g.2) h1) g.2
        simpa [mul_assoc] using h2
      have h1 : (⟨p, hpX⟩ : ↥X) ∈ P.subgroupOf X :=
        (Subgroup.mem_normalizer_iff.mp hg (⟨p, hpX⟩ : ↥X)).mpr (by
          rw [Subgroup.mem_subgroupOf]
          simpa using hp)
      exact Subgroup.mem_subgroupOf.mp h1
  · intro hg
    have hg' : (g : G) ∈ X ⊓ Subgroup.normalizer (P : Set G) :=
      Subgroup.mem_subgroupOf.mp hg
    obtain ⟨hgX, hgN⟩ := Subgroup.mem_inf.mp hg'
    have hgN' : (g : G) ∈ Subgroup.normalizer (P : Set G) := hgN
    rw [Subgroup.mem_normalizer_iff] at hgN' ⊢
    intro z
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
    have hconj : ((g * z * g⁻¹ : ↥X) : G) = (g : G) * (z : G) * (g : G)⁻¹ := rfl
    rw [hconj]
    exact hgN' (z : G)

theorem uc22r3e5c_barImage_inf_normalizer {X P : Subgroup G} (hPX : P ≤ X)
    (hO2 : pCoreOf 2 X ≤ P) :
    barImage X (X ⊓ Subgroup.normalizer (P : Set G)) =
      Subgroup.normalizer (barImage X P : Set (Bar2 X)) := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let π : ↥X →* Bar2 X := QuotientGroup.mk' (CFSG.pCore 2 ↥X)
  have hsub : (X ⊓ Subgroup.normalizer (P : Set G)).subgroupOf X =
      Subgroup.normalizer ((P.subgroupOf X : Subgroup ↥X) : Set ↥X) := by
    rw [← uc22r3e5c_normalizer_subgroupOf hPX]
  refine le_antisymm ?_ ?_
  · unfold barImage
    rw [hsub]
    exact Subgroup.le_normalizer_map π
  · let Y : Subgroup G := barPreimage X (Subgroup.normalizer (barImage X P : Set (Bar2 X)))
    have hYbar : barImage X Y = Subgroup.normalizer (barImage X P : Set (Bar2 X)) :=
      s13_barImage_barPreimage X _
    have hYle : Y ≤ X ⊓ Subgroup.normalizer (P : Set G) := by
      refine le_inf (s13_barPreimage_le X _) ?_
      exact uc22r3e5c_le_normalizer_of_barImage (s13_barPreimage_le X _) hPX hO2 hYbar.le
    calc Subgroup.normalizer (barImage X P : Set (Bar2 X))
        = barImage X Y := hYbar.symm
      _ ≤ barImage X (X ⊓ Subgroup.normalizer (P : Set G)) := barImage_mono hYle

end CFSG.LocalAnalysis.UniquenessCase.UC22

end
