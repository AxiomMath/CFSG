module

public import CFSG.RankThree.PartTwo.Sec4.T444.DiagRankI22

public section

namespace CFSG.RankThree.PartTwo.Sec4

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Assembly.RankThreeEven (projSL projSU)


section Certs


theorem ys03_N05_three_dvd_center_J {G : Type} [Group G] [Finite G] {A M H : Subgroup G} {s : G}
    {L J : Subgroup G} (h : DiagSetting G A M H s L) (hJ : J ∈ thetaComponents 3 G)
    (h3J : 3 ∣ Nat.card J) (hJL : ¬ J.map (starQuot G) ≤ L.map (starQuot G))
    (hL4 : Nonempty (↥(L.map (starQuot G)) ≃* Matrix.SpecialLinearGroup (Fin 3) (GaloisField 2 2)))
    (hZLJ : (Subgroup.center ↥(L.map (starQuot G))).map (L.map (starQuot G)).subtype ≤
      J.map (starQuot G)) :
    3 ∣ Nat.card (Subgroup.center ↥(J.map (starQuot G))) := by
  obtain ⟨e⟩ := hL4
  have hZ3 : Nat.card (Subgroup.center ↥(L.map (starQuot G))) = 3 :=
    CFSG.RankThree.PartTwo.KFacts.L34.card_center_of_mulEquiv e
  have hLc : CFSG.IsComponent (L.map (starQuot G)) :=
    isComponent_map_starQuot h.mem h.three_dvd
  have hJc : CFSG.IsComponent (J.map (starQuot G)) := isComponent_map_starQuot hJ h3J
  have hXY : ∀ x ∈ L.map (starQuot G), ∀ y ∈ J.map (starQuot G), Commute x y := by
    rcases CFSG.LocalCores.distinct_components_commute hLc hJc with hEq | hcomm
    · exact absurd (le_of_eq hEq.symm) hJL
    · exact ys03_I22_commute_of_bot hcomm
  obtain ⟨x, hx⟩ : ∃ x : ↥(Subgroup.center ↥(L.map (starQuot G))), orderOf x = 3 :=
    exists_prime_orderOf_dvd_card' 3 (dvd_of_eq hZ3.symm)
  have hyJ : x.1.1 ∈ J.map (starQuot G) :=
    hZLJ (Subgroup.mem_map.mpr ⟨x.1, x.2, rfl⟩)
  have hcy : ∀ g ∈ J.map (starQuot G), Commute x.1.1 g :=
    fun g hg => hXY _ x.1.2 g hg
  obtain ⟨w, hwZ, hw3⟩ : ∃ w ∈ Subgroup.center ↥(J.map (starQuot G)), orderOf w = 3 := by
    refine ⟨⟨x.1.1, hyJ⟩, ?_, ?_⟩
    · rw [Subgroup.mem_center_iff]
      intro g
      apply Subtype.ext
      exact (hcy g.1 g.2).symm.eq
    · rw [Subgroup.orderOf_mk, Subgroup.orderOf_coe, Subgroup.orderOf_coe, hx]
  have hw' : orderOf (⟨w, hwZ⟩ : ↥(Subgroup.center ↥(J.map (starQuot G)))) = 3 := by
    rw [Subgroup.orderOf_mk, hw3]
  have hdvd := orderOf_dvd_natCard (⟨w, hwZ⟩ : ↥(Subgroup.center ↥(J.map (starQuot G))))
  rw [hw'] at hdvd
  exact hdvd

end Certs

end CFSG.RankThree.PartTwo.Sec4

end
