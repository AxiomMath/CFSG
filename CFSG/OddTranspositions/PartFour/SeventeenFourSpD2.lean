module

public import CFSG.OddTranspositions.PartFour.RootLift
public import CFSG.OddTranspositions.PartFour.SpPlaneSL2

public section

namespace CFSG.OddTranspositions.PartFour

open CFSG.Timmesfeld CFSG.Timmesfeld.Bridge CFSG.Timmesfeld.Bridge.Asc72
open CFSG.Timmesfeld.Connectivity CFSG.LocalAnalysis.WeakClosure81.SevenK

variable {G : Type} [Group G] [Finite G] {D : Set G}

theorem blockLine_eq_insert_orbit_of_isSymplecticTransvection_of_two_le
    (h89 : PartThree.Lemma8_9) (h113 : PartThree.Theorem11_3) (hC : HypothesisC D)
    (hrad : ∀ N : Subgroup G, N.Normal → Group.IsSolvable N → N = ⊥)
    (hW : ¬ ∃ f n : ℕ, 2 ≤ f ∧ Nonempty (G ≃* L2Wreath f n))
    (hn3 : ¬ ∀ d ∈ D, ∀ e ∈ D, orderOf (d * e) ∈ ({1, 2, 3} : Set ℕ))
    (hMZ : ¬ CFSG.solvableRadical (Halpha D hC.alpha) ≤ Subgroup.center (Halpha D hC.alpha))
    (hHns : ¬ Group.IsSolvable (Halpha D hC.alpha))
    {s : Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha)} (hs : s ∈ imageClass hC)
    {k f : ℕ} (hk : 2 ≤ k)
    (hsp : IsSymplecticTransvection
      (Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha)) (2 * k) f s)
    {β : Set G} (hβ : β ∈ Dalpha D hC.alpha) :
    blockLine D hC.alpha β =
        insert hC.alpha ((fun x => cimg x β) '' (Malpha D hC.alpha : Set G)) ∧
      ((fun x => cimg x β) '' (Malpha D hC.alpha : Set G)).ncard = 2 ^ f := by
  obtain ⟨K0, hgen, hconj, hord⟩ :=
    exists_subgroup_of_isSymplecticTransvection (center_eq_bot_quotient_H hC) (by omega) hsp
  rw [← imageClass_eq_setOf_isConj hC hs] at hgen hconj hord
  exact blockLine_eq_insert_orbit_of_isSymplecticTransvection h89 h113 hC hrad hW hn3 hMZ hHns hs
    hk hsp hβ (two_pow_le_ncard_orbit_Malpha h89 h113 hC hrad hW hn3 hMZ hHns K0
      (pos_of_isSymplecticTransvection hsp) hgen hconj hord hβ)

end CFSG.OddTranspositions.PartFour
