module

public import CFSG.OddTranspositions.PartThree.Eleven.OneThree.MainCase.Defs
public import CFSG.OddTranspositions.HalphaQuotient
public import CFSG.Timmesfeld.Bridge.Asc72Lift

public section

namespace CFSG.OddTranspositions.PartThree.ElevenThree

open CFSG.Timmesfeld.Bridge.Asc72 CFSG.Timmesfeld.Connectivity CFSG.OddTranspositions.QZ
open CFSG.OddTranspositions.PartFour

variable {G : Type} [Group G] [Finite G] {D : Set G}

theorem disconnected_imageClass_of_disconnected_DstarH (hC : HypothesisC D)
    (hns : ¬ Group.IsSolvable (Halpha D hC.alpha)) (hdis : Disconnected (DstarH hC)) :
    Disconnected (imageClass hC) := by
  classical
  have hS : Setup (Halpha D hC.alpha) (DstarH hC) :=
    CFSG.OddTranspositions.PartThree.Nine.setup_DstarH hC
  have hRs : Group.IsSolvable (CFSG.solvableRadical (Halpha D hC.alpha)) :=
    CFSG.SignalizerFunctorTheorem.Nonsolvable.isSolvable_solvableRadical
  have hlift : ∀ a ∈ DstarH hC, ∀ b ∈ DstarH hC,
      a⁻¹ * b ∈ CFSG.solvableRadical (Halpha D hC.alpha) → Reach (DstarH hC) a b :=
    fun a ha b hb hab => reach_of_inv_mul_mem_solvable hS hns hRs ha hb hab
  obtain ⟨x, hx, y, hy, hxy⟩ := hdis
  refine ⟨QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)) x, ⟨x, hx, rfl⟩,
    QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)) y, ⟨y, hy, rfl⟩, ?_⟩
  intro h
  exact hxy (reach_of_reach_quotient (D := DstarH hC) hS.oddT hlift hx hy
    (by simpa [imageClass] using h))

end CFSG.OddTranspositions.PartThree.ElevenThree
