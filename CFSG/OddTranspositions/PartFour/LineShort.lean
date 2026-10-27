module

public import CFSG.OddTranspositions.PartFour.LinePolar

public section

namespace CFSG.OddTranspositions.PartFour

open CFSG.Timmesfeld CFSG.Timmesfeld.Bridge CFSG.Timmesfeld.Bridge.Asc72
open CFSG.Timmesfeld.Connectivity

variable {G : Type} [Group G] [Finite G] {D : Set G}

theorem false_of_ncard_perpMem_lineMem_le_two (h89 : PartThree.Lemma8_9)
    (h113 : PartThree.Theorem11_3) (hC : HypothesisC D)
    (hrad : ∀ N : Subgroup G, N.Normal → Group.IsSolvable N → N = ⊥)
    (hW : ¬ ∃ f n : ℕ, 2 ≤ f ∧ Nonempty (G ≃* L2Wreath f n))
    (hn3 : ¬ ∀ d ∈ D, ∀ e ∈ D, orderOf (d * e) ∈ ({1, 2, 3} : Set ℕ))
    (hMZ : ¬ CFSG.solvableRadical (Halpha D hC.alpha) ≤ Subgroup.center (Halpha D hC.alpha))
    {v w : Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha)}
    (hv : v ∈ imageClass hC) (hw : w ∈ imageClass hC) (hvw : Commute v w)
    (hne : perpMem (imageClass hC) v ≠ perpMem (imageClass hC) w)
    (h2 : (perpMem (imageClass hC) '' lineMem (imageClass hC) v w).ncard ≤ 2) : False := by
  obtain ⟨b, hbStar, -⟩ := id hv
  obtain ⟨β, hβ, -⟩ := mem_DalphaStar_iff.mp ((mem_DstarH_iff hC).mp hbStar)
  have hle := ncard_blockLine_le h89 h113 hC hrad hW hn3 hMZ hv hw hvw hne hβ
  have h3 := two_lt_encard_blockLine h89 h113 hC hrad hW hn3 hMZ hβ
  rw [← (Set.toFinite (blockLine D hC.alpha β)).cast_ncard_eq] at h3
  have : 2 < (blockLine D hC.alpha β).ncard := by exact_mod_cast h3
  omega

end CFSG.OddTranspositions.PartFour
