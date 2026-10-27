module

public import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoDefs
import CFSG.GroupTheory.ThreeTranspositions.NormalCores
import CFSG.LocalAnalysis.UniquenessCase.UC22P20h
import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GFldExcRed
import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch512FStar
import CFSG.HardMathSupport.RichardWeiss.RecognitionPresentation.StrongThree.Reduce
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Assembly.RankThreeEvenDefs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

open CFSG.Open Subgroup
open CFSG.Blueprint (LieModel)
open CFSG.LocalAnalysis.UniquenessCase.UC22

private theorem le_map_subtype_of_subgroupOf_le {Y : Type*} [Group Y] {X K : Subgroup Y}
    {E : Subgroup ↥X} (hKX : K ≤ X) (hKE : K.subgroupOf X ≤ E) : K ≤ E.map X.subtype := by
  intro k hk
  exact Subgroup.mem_map.mpr ⟨⟨k, hKX hk⟩, hKE hk, rfl⟩

private theorem map_subtype_eq_of_normalClosure_le {Y : Type*} [Group Y] {X K : Subgroup Y}
    {E : Subgroup ↥X} (hN : (E.map X.subtype).Normal)
    (hXK : X = Subgroup.normalClosure (K : Set Y)) (hK : K ≤ E.map X.subtype) :
    E.map X.subtype = X := by
  haveI : (E.map X.subtype).Normal := hN
  refine le_antisymm (Subgroup.map_subtype_le E) ?_
  calc X = Subgroup.normalClosure (K : Set Y) := hXK
    _ ≤ E.map X.subtype := Subgroup.normalClosure_le_normal fun s hs => hK hs

theorem isSimpleGroup_of_normalClosure (hSch : CFSG.AGLEmbedding.KFactCatalogSchreier)
    {Y : Type} [Group Y] [Finite Y] (hY : CFSG.Open.IsKGroup Y) (hO : CFSG.pPrimeCore 3 Y = ⊥)
    {X K : Subgroup Y} (hX3 : Open.pRank 3 X ≤ 1) (hXK : X = normalClosure (K : Set Y))
    (hK : ⁅K, K⁆ = K) (hK1 : K ≠ ⊥) : IsSimpleGroup X ∧ ∃ a b : X, a * b ≠ b * a := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : X.Normal := by rw [hXK]; infer_instance
  have hKX : K ≤ X := by rw [hXK]; exact Subgroup.le_normalClosure
  set K' : Subgroup ↥X := K.subgroupOf X with hK'def
  have hK'perf : ⁅K', K'⁆ = K' := by
    apply Subgroup.map_injective X.subtype_injective
    rw [hK'def, Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hKX, hK]
  have hK'ne : K' ≠ ⊥ := by
    intro hbot
    apply hK1
    rw [← Subgroup.map_subgroupOf_eq_of_le hKX, ← hK'def, hbot, Subgroup.map_bot]
  have hO' : CFSG.pPrimeCore 3 ↥X = ⊥ :=
    CFSG.GroupTheory.ThreeTranspositions.pPrimeCore_eq_bot_of_normal Nat.prime_three hO X
  have hX3' : Open.pRank 3 (⊤ : Subgroup ↥X) ≤ 1 := by
    rw [← CFSG.SectionRank.pRank_eq_pRank_top_subgroup X]
    exact hX3
  have hns : ¬ Group.IsSolvable ↥X := by
    intro hsol
    haveI : Group.IsSolvable ↥X := hsol
    exact CFSG.LocalAnalysis.GLTheoremA.Y10GField.solvable_no_perfect
      (C := ⊤) (Q := K') inferInstance le_top hK'perf hK'ne
  obtain ⟨E, hEcomp, hFE, hEsimp, hEnab, hEcen⟩ :=
    CFSG.LocalAnalysis.WeakClosure81.exists_generalizedFitting_eq_isComponent hO' hX3' hns
  obtain ⟨hEchar, hEnorm⟩ :=
    hFE ▸ CFSG.LocalCores.generalized_fitting_characteristic (G := ↥X)
  haveI : E.Characteristic := hEchar
  haveI : E.Normal := hEnorm
  have hout : Group.IsSolvable (CFSG.ComponentClassification.OuterAutomorphisms.Outer ↥E) :=
    CFSG.LocalAnalysis.GLTheoremB.outer_solvable_of_component hSch (hY.subgroup X)
      ((CFSG.isComponent_iff_open E).mp hEcomp)
  have hKE : K' ≤ E :=
    CFSG.HardMathSupport.RichardWeiss.RecognitionPresentation.StrongThree.perfect_le_of_outer
      hEcen hout hK'perf
  have hEnormY : (E.map X.subtype).Normal := uc22p20h_normal_map_of_char X E
  have hKle : K ≤ E.map X.subtype := le_map_subtype_of_subgroupOf_le hKX hKE
  have hmap : E.map X.subtype = X := map_subtype_eq_of_normalClosure_le hEnormY hXK hKle
  have htop : (⊤ : Subgroup ↥X).map X.subtype = X := by
    refine le_antisymm (Subgroup.map_subtype_le ⊤) ?_
    intro x hx
    exact ⟨⟨x, hx⟩, trivial, rfl⟩
  have hEtop : E = ⊤ :=
    Subgroup.map_injective X.subtype_injective (by rw [hmap, htop])
  subst hEtop
  refine ⟨?_, ?_⟩
  · exact (Subgroup.topEquiv (G := ↥X)).isSimpleGroup_congr.mp hEsimp
  · obtain ⟨a, b, hab⟩ := hEnab
    exact ⟨Subgroup.topEquiv a, Subgroup.topEquiv b,
      fun h => hab ((Subgroup.topEquiv (G := ↥X)).injective h)⟩

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8
