module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S21rR3E5CCartanA
public import CFSG.GroupTheory.PCore.OpenTransport
public import CFSG.LocalAnalysis.UniquenessCase.UC22S21a
public import CFSG.RankThree.PartTwo.Sec3.TwoThreeStructure

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup
open CFSG.QuasithinUnique (IsSylowTwoOf)
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem uc22r3e5c_card_core_mul_card_barImage {X Y : Subgroup G} (hYX : Y ≤ X)
    (hQY : pCoreOf 2 X ≤ Y) :
    Nat.card (pCoreOf 2 X) * Nat.card (barImage X Y) = Nat.card Y := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let π : ↥X →* Bar2 X := QuotientGroup.mk' (CFSG.pCore 2 ↥X)
  have hπker : π.ker = CFSG.pCore 2 ↥X := QuotientGroup.ker_mk' _
  have h := uc22r3e5c_card_ker_mul_card_map π (Y.subgroupOf X)
  have hbar : (Y.subgroupOf X).map π = barImage X Y := rfl
  have hYs : Nat.card ↥(Y.subgroupOf X) = Nat.card Y :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hYX)
  have hker : Nat.card ↥(π.ker ⊓ Y.subgroupOf X) = Nat.card (pCoreOf 2 X) := by
    have hEq : π.ker ⊓ Y.subgroupOf X = π.ker := by
      rw [hπker]
      exact inf_eq_left.mpr fun x hx =>
        Subgroup.mem_subgroupOf.mpr (hQY ((CFSG.mem_openPCoreOf_iff (p := 2) (H := X) x).mpr hx))
    rw [hEq, hπker]
    exact (Subgroup.card_map_of_injective (K := CFSG.pCore 2 ↥X) X.subtype_injective).symm
  rw [hbar, hYs, hker] at h
  exact h

end CFSG.LocalAnalysis.UniquenessCase.UC22

end
