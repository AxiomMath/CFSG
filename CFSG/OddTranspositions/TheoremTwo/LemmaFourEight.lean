module

public import CFSG.OddTranspositions.TheoremTwo.StepSeven
public import CFSG.OddTranspositions.TheoremTwo.WCover

public section

namespace CFSG.OddTranspositions.QZ

open CFSG.Timmesfeld CFSG.Timmesfeld.Bridge CFSG.Timmesfeld.Bridge.Asc72
open CFSG.Timmesfeld.Connectivity CFSG.OddTranspositions CFSG.GroupTheory

variable {G : Type} [Group G] [Finite G] {D : Set G} {u w v z a : G} {K₁ S' : Subgroup G}

namespace Config

theorem false_of_connected_of_prop47
    (hQ : Config D u w v z a K₁ S') (hC : HypothesisC D) (hu : u ∈ hC.alpha)
    (hv : v ∈ DalphaStar D hC.alpha) (hmin : SmallerTwoStar (Nat.card G))
    (hfib : ∀ (ε : (Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha)) ≃*
        Equiv.Perm (Fin 5)),
      ε '' imageClass hC = transpositions →
      ∀ (d : G) (hd : d ∈ DalphaStar D hC.alpha)
        (d' : G) (hd' : d' ∈ DalphaStar D hC.alpha),
        ε (starImage hC d hd) = ε (starImage hC d' hd') → d = d')
    {e : G} (he2 : orderOf e = 2) (he : e ∉ Subgroup.zpowers z)
    (hzK : thirdK D z ≤ Subgroup.centralizer ({e} : Set G))
    (haK : thirdK D a ≤ Subgroup.centralizer ({e} : Set G))
    (hconn : ¬ Disconnected (barOmega D e)) : False := by
  classical
  let Y : Subgroup G := thirdK D e
  let O : Subgroup Y := CFSG.solvableRadical Y
  have hYne : Y ≠ ⊤ := thirdK_e_ne_top hQ he2
  have hcard : Nat.card (Y ⧸ O) < Nat.card G := by
    have h1 : Nat.card Y < Nat.card G := by
      simpa using Subgroup.card_lt_of_lt (lt_top_iff_ne_top.mpr hYne)
    have h2 : Nat.card (Y ⧸ O) ≤ Nat.card Y :=
      Nat.card_le_card_of_surjective (QuotientGroup.mk' O) (QuotientGroup.mk'_surjective O)
    omega
  have hradY : ∀ N : Subgroup (Y ⧸ O), N.Normal → Group.IsSolvable N → N = ⊥ :=
    fun N hN hNs => OddTransp.eq_bot_of_quotient_solvableRadical N hN hNs
  have hsetup : Setup (Y ⧸ O) (barOmega D e) := setup_barOmega hQ he hzK haK
  have hlocal : LocalSecond (barOmega D e) := localSecond_barOmega hQ he hzK haK
  rcases hmin (Y ⧸ O) (barOmega D e) hcard hsetup hconn hradY hlocal with h3 | hO4
  · exact false_of_connected_of_threeTransposition hQ hC hu hv he2 he hzK haK h3
  · have hXD : Subgroup.closure ((Y : Set G) ∩ D) = Y := by
      show Subgroup.closure ((thirdK D e : Set G) ∩ D) = thirdK D e
      rw [thirdK]
      congr 1
      ext x
      constructor
      · rintro ⟨hxY, hxD⟩
        exact mem_Delta_iff.mpr ⟨hxD,
          Subgroup.mem_centralizer_singleton_iff.mp (thirdK_le_centralizer hxY)⟩
      · intro hx
        exact ⟨Delta_subset_thirdK hx, (mem_Delta_iff.mp hx).1⟩
    have hKX : thirdK D z ≤ Y := thirdK_le_thirdK_of_le_centralizer hzK
    have hsolvO : Group.IsSolvable (↥O) := OddTransp.isSolvable_solvableRadical (G := Y)
    have hPX : O4PairData (Y ⧸ O) (Omega D Y O) := by
      simpa [Omega, Config.barOmega_eq_image, Y, O] using hO4
    have hDα : DalphaStar D hC.alpha ⊆ (Y : Set G) :=
      DalphaStar_subset_X_of_prop47 hC hQ hmin hQ.tri hu hv hsolvO hKX hPX hfib
    exact hYne (o4Close_of_DalphaStar hC hQ.tri hu hv hQ.third Y hXD hKX hDα)

theorem centralizer_thirdK_eq_of_prop47
    (hQ : Config D u w v z a K₁ S') (hC : HypothesisC D) (hu : u ∈ hC.alpha)
    (hv : v ∈ DalphaStar D hC.alpha) (hmin : SmallerTwoStar (Nat.card G))
    (hfib : ∀ (ε : (Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha)) ≃*
        Equiv.Perm (Fin 5)),
      ε '' imageClass hC = transpositions →
      ∀ (d : G) (hd : d ∈ DalphaStar D hC.alpha)
        (d' : G) (hd' : d' ∈ DalphaStar D hC.alpha),
        ε (starImage hC d hd) = ε (starImage hC d' hd') → d = d') :
    S' ⊓ Subgroup.centralizer (thirdK D z : Set G) = Subgroup.zpowers z := by
  have hzK : z ∈ Subgroup.centralizer (thirdK D z : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    exact Subgroup.mem_centralizer_singleton_iff.mp (thirdK_le_centralizer hh)
  have hle : Subgroup.zpowers z ≤ S' ⊓ Subgroup.centralizer (thirdK D z : Set G) :=
    (Subgroup.zpowers_le).mpr ⟨hQ.z_central.1, hzK⟩
  refine ((lt_or_eq_of_le hle).resolve_left fun hB => ?_).symm
  obtain ⟨e, he2, he, hzK', haK'⟩ := hQ.exists_inv_centralizing hB
  by_cases hd : Disconnected (barOmega D e)
  · exact hQ.false_of_disconnected hmin he2 he hzK' haK' hd
  · exact false_of_connected_of_prop47 hQ hC hu hv hmin hfib he2 he hzK' haK' hd

end Config

end CFSG.OddTranspositions.QZ

end
