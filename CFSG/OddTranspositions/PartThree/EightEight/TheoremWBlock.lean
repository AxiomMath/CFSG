module

public import CFSG.OddTranspositions.HalphaQuotient
public import CFSG.OddTranspositions.PartThree.EightEight.Star
import CFSG.OddTranspositions.PartThree.EightEight.StarBlockMeet

public section

namespace CFSG.OddTranspositions.PartThree.EightEight

open CFSG.Timmesfeld.Bridge.Asc72 CFSG.OddTranspositions.QZ

variable {G : Type} [Group G] [Finite G] {D : Set G}

theorem exists_mem_Dalpha_mem_DalphaStar_of_commute (h86 : Lemma8_6) (h87 : Theorem8_7)
    (hC : HypothesisC (G := G) D)
    (hrad : ∀ N : Subgroup G, N.Normal → Group.IsSolvable N → N = ⊥)
    (hO4 : ¬ O4PairData G D) (hF : FaithfulOnBlocks hC.alpha)
    (hne : derivedSeries (Halpha D hC.alpha) 1 ≠ derivedSeries (Halpha D hC.alpha) 2)
    {x w y : G} (hx : x ∈ DalphaStar D hC.alpha)
    (hw : w ∈ DalphaStar D hC.alpha) (hy : y ∈ DalphaStar D hC.alpha)
    {d : Halpha D hC.alpha} (hd : d ∈ DstarH hC) (hdx : Commute (d : G) x)
    (hdy : Commute (d : G) y) (hdw : Commute (d : G) w) (hdxne : (d : G) ≠ x)
    (hdyne : (d : G) ≠ y) (hdwne : (d : G) ≠ w) :
    ∃ (ρ : Set G) (_ : ρ ∈ Dalpha D hC.alpha) (_ : (d : G) ∈ ρ),
      x ∈ DalphaStar D ρ ∧ w ∈ DalphaStar D ρ ∧ y ∈ DalphaStar D ρ := by
  obtain ⟨ρ, hρ, hdρ⟩ := (mem_DstarH_iff hC).mp hd
  have key : ∀ p ∈ DalphaStar D hC.alpha, (d : G) ≠ p → Commute (d : G) p →
      p ∈ DalphaStar D ρ := by
    rintro p ⟨γ, hγ, hpγ⟩ hdp hcomm
    exact ⟨γ, (mem_Dalpha_iff_commute h86 h87 hC hrad hO4 hF hne hρ.1 hγ.1 hdρ hpγ hdp).mpr
      hcomm, hpγ⟩
  exact ⟨ρ, hρ, hdρ, key x hx hdxne hdx, key w hw hdwne hdw, key y hy hdyne hdy⟩

theorem exists_mem_Dalpha_mem_DalphaStar_of_isTriangle (h86 : Lemma8_6) (h87 : Theorem8_7)
    (hC : HypothesisC (G := G) D)
    (hrad : ∀ N : Subgroup G, N.Normal → Group.IsSolvable N → N = ⊥)
    (hO4 : ¬ O4PairData G D) (hF : FaithfulOnBlocks hC.alpha)
    (hne : derivedSeries (Halpha D hC.alpha) 1 ≠ derivedSeries (Halpha D hC.alpha) 2)
    {x w y : G} (ht : IsTriangle D x w y) (hx : x ∈ DalphaStar D hC.alpha)
    (hw : w ∈ DalphaStar D hC.alpha) (hy : y ∈ DalphaStar D hC.alpha)
    {d : Halpha D hC.alpha} (hd : d ∈ DstarH hC) (hdx : Commute (d : G) x)
    (hdy : Commute (d : G) y) (hdw : Commute (d : G) w) :
    ∃ (ρ : Set G) (_ : ρ ∈ Dalpha D hC.alpha) (_ : (d : G) ∈ ρ),
      x ∈ DalphaStar D ρ ∧ w ∈ DalphaStar D ρ ∧ y ∈ DalphaStar D ρ :=
  exists_mem_Dalpha_mem_DalphaStar_of_commute h86 h87 hC hrad hO4 hF hne hx hw hy hd hdx hdy hdw
    (fun h => ht.2.2.2.2.2.1 (h ▸ hdw)) (fun h => ht.2.2.2.2.2.2 (h ▸ hdw))
    (fun h => ht.2.2.2.2.2.1 (h ▸ hdx).symm)

end CFSG.OddTranspositions.PartThree.EightEight
