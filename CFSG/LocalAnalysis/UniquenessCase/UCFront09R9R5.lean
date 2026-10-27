module

public import CFSG.LocalAnalysis.UniquenessCase.UCFront09b
import CFSG.LocalAnalysis.RankThreeUC.ProofSupport.ResidualTwoExtension.ResidualTwoExtension
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Fourteen4Aux
import CFSG.LocalAnalysis.UniquenessCase.UCFront09R912A5
import CFSG.LocalAnalysis.UniquenessCase.UCFront09R98W

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.F09

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC CFSG.LocalAnalysis.RankThreeUC.ProofSupport Subgroup
open CFSG.ABGLocalTools (IsSylowOf)

variable {G : Type} [Group G] [Finite G]

theorem opp_eq_L9_and_isSylowOf (D : Data G) {Y W N S : Subgroup G} (hY : Y ∈ calY2Star9 D)
    (hYW : Y ≤ W) (hWM : W ≤ D.M) (hN : N ∈ calMOf W) (hNM : N ≠ D.M) (hS : IsSylowOf 2 S Y) :
    Opp 3 Y = L9 Y W ∧ IsSylowOf 2 S W := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hYmax : Maximal (· ∈ calY2_9 D) Y := hY
  have hSW : S ≤ W := hS.le.trans hYW
  obtain ⟨Q, hQ⟩ := (hS.isPGroup.comap_subtype (K := W)).exists_le_sylow
  obtain ⟨P, hP, hSP⟩ : ∃ P : Subgroup G, IsSylowOf 2 P W ∧ S ≤ P :=
    ⟨_, ⟨Q, rfl⟩, fun s hs => mem_map.2 ⟨⟨s, hSW hs⟩, hQ (mem_subgroupOf.2 hs), rfl⟩⟩
  have hYKP : Y ≤ L9 Y W ⊔ P :=
    le_of_le_of_isSylowOf ((opp_le_L9 Y W).trans le_sup_left) (hSP.trans le_sup_right) hS
      hYmax.prop.2.2.2.2
  have hYeq : Y = L9 Y W ⊔ P :=
    hYmax.eq_of_le (sup_mem_calY2_9 D hYmax.prop hYW hWM hN hNM hP.isPGroup hP.le hYKP) hYKP
  refine ⟨(congrArg (Opp 3) hYeq).trans (opp_L9_sup_eq hYW hP.le hP.isPGroup), ?_⟩
  rw [← hS.eq_of_le hSP (le_sup_right.trans hYeq.ge) hP.isPGroup]
  exact hP

theorem r9R5_holds (D : Data G) : R9R5 D := by
  intro Y H D₃ S hY
  obtain ⟨⟨hY9, ⟨hYH, hHM, -⟩, -, -⟩, hY2, ⟨-, hF⟩, hS⟩ := hY
  obtain ⟨N, hN, hHN⟩ := PartTwo.exists_isMaxTwoLocal_ge_of_fstar hF
    (fun h => hHM (h ▸ bot_le))
  have hYW : Y ≤ H ⊓ D.M := le_inf hYH hY9.1
  obtain ⟨hX, hSW⟩ := opp_eq_L9_and_isSylowOf D hY2 hYW inf_le_right
    ⟨hN, inf_le_left.trans hHN⟩ (fun h => hHM (h ▸ hHN)) hS
  refine ⟨?_, hSW⟩
  rw [hX]
  refine (normal_subgroupOf_iff_le_normalizer ?_).2
    (ResidualTwoExtension.le_normalizer_normalClosureUnder (Opp 3 Y) (H ⊓ D.M))
  refine iSup_le fun w => ?_
  rintro _ ⟨x, hx, rfl⟩
  have hxW : x ∈ H ⊓ D.M := hYW (opp_le_self 3 Y hx)
  exact (H ⊓ D.M).mul_mem ((H ⊓ D.M).mul_mem w.2 hxW) ((H ⊓ D.M).inv_mem w.2)

theorem r910_holds (D : Data G) : R910 D := by
  rintro Y hY B - hBY hBn ⟨S, hS, hSn⟩
  have hYmax : Maximal (· ∈ calY2_9 D) Y := hY
  have hYW : Y ≤ D.M ⊓ normalizer (B : Set G) :=
    le_inf hYmax.prop.1.1 ((normal_subgroupOf_iff_le_normalizer hBY).1 hBn)
  by_contra h
  obtain ⟨N, hN, hNM⟩ : ∃ N ∈ calMOf (D.M ⊓ normalizer (B : Set G)), N ≠ D.M := by
    by_contra h'
    exact h (Set.eq_singleton_iff_unique_mem.2 ⟨⟨D.maxLocal, inf_le_left⟩,
      fun N hN => Classical.byContradiction fun hNM => h' ⟨N, hN, hNM⟩⟩)
  exact hSn (opp_eq_L9_and_isSylowOf D hY hYW inf_le_left hN hNM hS).2

end CFSG.LocalAnalysis.UniquenessCase.UC22.F09
