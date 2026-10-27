module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenSmallDefs
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC34Aut

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

theorem s16c34_exists_star_transvection (D : Data G) (h1217 : R1217 D) {V₀ V L : Subgroup G}
    (h : Hyp151 D V₀ V L) (hL : barSub V₀ V h.isElemAbelian L ≠ ⊥)
    (hγ : gamma15 D.M V₀ V h.isElemAbelian L ≤ 3)
    (hev : Even (Nat.card ↥(barSub V₀ V h.isElemAbelian L))) :
    ∃ φ ∈ Mbar D.M (v1Sub D.M V₀ V h.isElemAbelian L) V h.isElemAbelian,
      InducesTransvection φ (wStar D.M V₀ V h.isElemAbelian L) := by
  have hcard : Nat.card ↥(s15AW h) = Nat.card ↥(barSub V₀ V h.isElemAbelian L) :=
    (Nat.card_congr (s15AWEquiv h1217 h hL).toEquiv).symm
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨a, ha⟩ := exists_prime_orderOf_dvd_card' (G := ↥(s15AW h)) 2
    (even_iff_two_dvd.1 (hcard ▸ hev))
  have ha2 : orderOf (a : MulAut ↥(wStar D.M V₀ V h.isElemAbelian L)) = 2 := by
    rw [Subgroup.orderOf_coe]
    exact ha
  have htr := s16c34_inducesTransvection_of_involution (s15_Three_wStar_exp h) hγ ha2
  obtain ⟨g, hgL, hga⟩ := mem_autSub.1 a.2
  have hφM : (g : MulAut (vStar D.M V₀ V h.isElemAbelian L)) ∈
      Mbar D.M (v1Sub D.M V₀ V h.isElemAbelian L) V h.isElemAbelian :=
    barSub_mono (v1Sub D.M V₀ V h.isElemAbelian L) V h.isElemAbelian h.le hgL
  refine ⟨g, hφM, s16c34_inducesTransvection_of_resHom g.2 ?_⟩
  rw [show (⟨(g : MulAut (vStar D.M V₀ V h.isElemAbelian L)), g.2⟩ :
    stabSub (wStar D.M V₀ V h.isElemAbelian L)) = g from rfl, hga]
  exact htr

theorem s16c34_desc153_of_even (D : Data G) (h1217 : R1217 D) (h153 : R15_3Small D)
    {V₀ V L : Subgroup G} (h : Hyp151 D V₀ V L) (hsmall : mSub V₀ ≤ 2)
    (hL : barSub V₀ V h.isElemAbelian L ≠ ⊥)
    (hγ : gamma15 D.M V₀ V h.isElemAbelian L ≤ 3)
    (hev : Even (Nat.card ↥(barSub V₀ V h.isElemAbelian L))) :
    Desc153 D V₀ V h.isElemAbelian L :=
  h153 V₀ V L h hsmall (s16c34_exists_star_transvection D h1217 h hL hγ hev)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
