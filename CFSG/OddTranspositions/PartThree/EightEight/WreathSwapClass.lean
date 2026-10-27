module

public import CFSG.OddTranspositions.HalphaQuotient
public import CFSG.OddTranspositions.PartThree.Ten.WreathEndgame
import CFSG.OddTranspositions.PartThree.EightEight.WreathNatural
public import CFSG.Timmesfeld.Bridge.Asc72Lift

public section

namespace CFSG.OddTranspositions.PartThree.EightEight

open CFSG.Timmesfeld.Bridge.Asc72

variable {G : Type} [Group G] [Finite G] {D : Set G}

theorem mem_swapSet_of_mem_DstarH (hC : HypothesisC D)
    (hns : ¬ Group.IsSolvable (Halpha D hC.alpha)) {f k : ℕ} (hf : 2 ≤ f) (hk : k = 3 ∨ k = 4)
    (φ : (Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha)) ≃* L2Wreath f k)
    {a : Halpha D hC.alpha} (ha : a ∈ DstarH hC) :
    φ (QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)) a) ∈
      WreathEndgame.swapSet f k := by
  have hmem : QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)) a ∈ imageClass hC :=
    ⟨a, ha, rfl⟩
  rw [eq_preimage_swapSet_of_mulEquiv (setup_quotient hC hns) hf hk φ] at hmem
  exact hmem

theorem exists_mem_DstarH_eq_of_mem_swapSet (hC : HypothesisC D)
    (hns : ¬ Group.IsSolvable (Halpha D hC.alpha)) {f k : ℕ} (hf : 2 ≤ f) (hk : k = 3 ∨ k = 4)
    (φ : (Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha)) ≃* L2Wreath f k)
    {s : L2Wreath f k} (hs : s ∈ WreathEndgame.swapSet f k) :
    ∃ d ∈ DstarH hC, φ (QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)) d) = s := by
  have hmem : φ.symm s ∈ imageClass hC := by
    rw [eq_preimage_swapSet_of_mulEquiv (setup_quotient hC hns) hf hk φ]
    simpa only [Set.mem_preimage, MulEquiv.apply_symm_apply] using hs
  obtain ⟨d, hd, hdeq⟩ := hmem
  exact ⟨d, hd, by rw [hdeq, MulEquiv.apply_symm_apply]⟩

end CFSG.OddTranspositions.PartThree.EightEight
