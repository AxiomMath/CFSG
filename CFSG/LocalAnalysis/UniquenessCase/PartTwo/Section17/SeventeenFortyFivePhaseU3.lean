module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenFortyFivePhaseProps
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.UnitaryOddIndex

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17.SzFive

open Subgroup

theorem k45UnitaryThirtyOneGen_holds : K45UnitaryThirtyOneGen := by
  intro X _ _ L A₁ T d hLd hd hA₁L hA₁ hTL
  have : Fact (Nat.Prime 31) := ⟨by norm_num⟩
  have hst : CFSG.Open.StatedClassicalModel ↥L .PSU 3 31 d.1.fieldExponent :=
    CFSG.AGLEmbedding.UnitaryModel.statedClassicalModel (p := 31) hd hLd
  obtain ⟨S, hS⟩ := hTL
  let A : Subgroup ↥L := A₁.subgroupOf L
  have hAcard : Nat.card A = 31 := by
    change Nat.card (A₁.subgroupOf L) = 31
    rw [← hA₁]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hA₁L).toEquiv
  have hAp : IsPGroup 31 A := IsPGroup.of_card (n := 1) (by rw [pow_one]; exact hAcard)
  have : IsCyclic A := isCyclic_of_prime_card (p := 31) hAcard
  have : IsMulCommutative A := IsCyclic.isMulCommutative
  obtain ⟨C, hC, hAC, htop⟩ :=
    CFSG.AGLEmbedding.UnitaryModel.exists_isMulCommutative_sylow_two_sup_normalizer_eq_top
      (p := 31) (f := d.1.fieldExponent) (by norm_num) hst hAp S
  have : IsMulCommutative C := hC
  refine ⟨C.map L.subtype, Subgroup.map_isMulCommutative C L.subtype, ?_, ?_⟩
  · exact (Subgroup.map_subgroupOf_eq_of_le hA₁L).symm.le.trans (Subgroup.map_mono hAC)
  · intro x hx
    have hmap :
        ((S : Subgroup ↥L) ⊔ Subgroup.normalizer (C : Set ↥L)).map L.subtype ≤
          (T ⊓ L) ⊔
            (L ⊓ Subgroup.normalizer ((C.map L.subtype : Subgroup X) : Set X)) := by
      rw [Subgroup.map_sup, hS]
      refine sup_le le_sup_left ((le_inf ?_ ?_).trans le_sup_right)
      · exact Subgroup.map_subtype_le (Subgroup.normalizer (C : Set ↥L))
      · exact Subgroup.le_normalizer_map (H := C) L.subtype
    have hx' : x ∈ ((S : Subgroup ↥L) ⊔ Subgroup.normalizer (C : Set ↥L)).map L.subtype := by
      rw [htop, Subgroup.map_top, Subgroup.range_subtype]
      exact hx
    exact hmap hx'

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17.SzFive

end
