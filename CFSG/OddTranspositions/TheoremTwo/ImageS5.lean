module

public import CFSG.OddTranspositions.HalphaS5
public import CFSG.OddTranspositions.O4FibresAssembly
public import CFSG.OddTranspositions.TheoremTwo.ImageConnected
public import CFSG.Timmesfeld.Bridge.RootSetsConn3

public section

namespace CFSG.OddTranspositions

open CFSG.Timmesfeld.Bridge Asc72 OddTransp CFSG.Timmesfeld.Connectivity CFSG.GroupTheory
open CFSG.OddTranspositions.QZ

variable {G : Type} [Group G] [Finite G] {D : Set G} {u w v z a : G} {K₁ S' : Subgroup G}

theorem not_disconnected_imageClass_of_config
    (hC : HypothesisC D) (hQ : Config D u w v z a K₁ S')
    (hmin : SmallerTwoStar (Nat.card G))
    (htri : IsTriangle D u w v) (hu : u ∈ hC.alpha) (hv : v ∈ DalphaStar D hC.alpha)
    {X : Subgroup G} {R : Subgroup X} [R.Normal] (hR : Group.IsSolvable R)
    (hKX : thirdK D z ≤ X) (hPX : O4PairData (X ⧸ R) (Omega D X R)) :
    ¬ Disconnected (imageClass hC) := by
  have hHns : ¬ Group.IsSolvable (Halpha D hC.alpha) :=
    not_isSolvable_Halpha_of_config hC hQ htri hu hv hR hKX hPX
  have hrad : ∀ N : Subgroup (Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha)),
      N.Normal → Group.IsSolvable N → N = ⊥ := by
    intro N hN hNs
    have hle : N ≤ CFSG.solvableRadical
        (Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha)) :=
      le_solvableRadical hN hNs
    rw [solvableRadical_quotient_H hC] at hle
    exact le_bot_iff.mp hle
  exact not_disconnected_of_smallerTwoStar (setup_quotient hC hHns) hrad
    (localSecond_imageClass hC hQ.local2 hHns) (widthLe_imageClass_two hC
        (widthLe_three_of_config hQ)) hmin
    (card_quotient_Halpha_lt hC hQ.rad)

theorem imageClass_S5_of_config
    (hC : HypothesisC D) (hQ : Config D u w v z a K₁ S')
    (hmin : SmallerTwoStar (Nat.card G))
    (htri : IsTriangle D u w v) (hu : u ∈ hC.alpha) (hv : v ∈ DalphaStar D hC.alpha)
    {X : Subgroup G} {R : Subgroup X} [R.Normal] (hR : Group.IsSolvable R)
    (hKX : thirdK D z ≤ X) (hPX : O4PairData (X ⧸ R) (Omega D X R)) :
    ∃ e : (Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha)) ≃*
        Equiv.Perm (Fin 5),
      e '' imageClass hC = transpositions :=
  imageClass_S5' hC hQ hmin
    (not_disconnected_imageClass_of_config hC hQ hmin htri hu hv hR hKX hPX)
    htri hu hv hR hKX hPX

theorem DalphaStar_subset_X_of_fibres
    (hC : HypothesisC D) (hQ : Config D u w v z a K₁ S')
    (hmin : SmallerTwoStar (Nat.card G))
    (htri : IsTriangle D u w v) (hu : u ∈ hC.alpha) (hv : v ∈ DalphaStar D hC.alpha)
    {X : Subgroup G} {R : Subgroup X} [R.Normal] (hR : Group.IsSolvable R)
    (hKX : thirdK D z ≤ X) (hPX : O4PairData (X ⧸ R) (Omega D X R))
    {Wset : Set X} (hWmem : ∀ w ∈ Wset, (w : G) ∈ DalphaStar D hC.alpha)
    (hWcover : ∀ (e : (Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha)) ≃*
        Equiv.Perm (Fin 5)),
      e '' imageClass hC = transpositions → ∀ τ ∈ transpositions,
        ∃ (w : X) (hw : w ∈ Wset),
          e (starImage hC (w : G) (hWmem w hw)) = τ)
    (hfib : ∀ (e : (Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha)) ≃*
        Equiv.Perm (Fin 5)),
      e '' imageClass hC = transpositions →
      ∀ (d : G) (hd : d ∈ DalphaStar D hC.alpha)
        (d' : G) (hd' : d' ∈ DalphaStar D hC.alpha),
        e (starImage hC d hd) = e (starImage hC d' hd') → d = d') :
    DalphaStar D hC.alpha ⊆ (X : Set G) := by
  obtain ⟨e, he⟩ := imageClass_S5_of_config hC hQ hmin htri hu hv hR hKX hPX
  exact DalphaStar_subset_X_of_singleton_fibres hC he hWmem (hWcover e he) (hfib e he)

end CFSG.OddTranspositions

end
