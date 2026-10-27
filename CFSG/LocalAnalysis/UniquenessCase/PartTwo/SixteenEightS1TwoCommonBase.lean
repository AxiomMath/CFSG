module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightS1TwoCommonA
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightS1Star

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

abbrev s16e_two_NatPred (W : Type) [CommGroup W] : Type :=
  Subgroup (MulAut W) → Subgroup W → Subgroup W → Prop

structure s16e_two_Fam {G : Type} [Group G] [Finite G] (D : Data G) (V₀ V L : Subgroup G)
    (hV : IsElemAbelian 2 V) (P : s16e_two_NatPred (vStar D.M V₀ V hV L)) : Prop where
  natFacts : s16e_two_NatFacts P (lStar D.M V₀ V hV L)
  simple : IsSimpleGroup ↥(lBar V₀ V hV L)
  perfect : ⁅lBar V₀ V hV L, lBar V₀ V hV L⁆ = lBar V₀ V hV L
  sum : SumOfNat P (lStar D.M V₀ V hV L) (wStar D.M V₀ V hV L) ⊥ 2

section Transport

theorem s16e_two_lStar_equiv (D : Data G) (h1217 : R1217 D) {V₀ V L : Subgroup G}
    (h : Hyp151 D V₀ V L) (hV : IsElemAbelian 2 V) :
    Nonempty (↥(lStar D.M V₀ V hV L) ≃* ↥(lBar V₀ V hV L)) := by
  obtain ⟨ρ, -, hρ⟩ := s16e_star_equiv D h1217 h hV
  have hLX : lBar V₀ V hV L ≤ Mbar D.M V₀ V hV := barSub_mono V₀ V hV h.le
  have hLX' : lStar D.M V₀ V hV L ≤ Mbar D.M (v1Sub D.M V₀ V hV L) V hV :=
    barSub_mono _ V hV h.le
  exact ⟨(((Subgroup.subgroupOfEquivOfLe hLX').symm.trans
    (MulEquiv.subgroupCongr hρ.symm)).trans
    (MulEquiv.subgroupMap ρ _).symm).trans (Subgroup.subgroupOfEquivOfLe hLX)⟩

theorem s16e_two_lStar_le (D : Data G) {V₀ V L : Subgroup G} (h : Hyp151 D V₀ V L)
    (hV : IsElemAbelian 2 V) :
    lStar D.M V₀ V hV L ≤ Mbar D.M (v1Sub D.M V₀ V hV L) V hV :=
  barSub_mono _ V hV h.le

theorem s16e_two_lBar_le (D : Data G) {V₀ V L : Subgroup G} (h : Hyp151 D V₀ V L)
    (hV : IsElemAbelian 2 V) : lBar V₀ V hV L ≤ Mbar D.M V₀ V hV :=
  barSub_mono V₀ V hV h.le

theorem s16e_two_kappa_equiv (D : Data G) (h1217 : R1217 D) {V₀ V L : Subgroup G}
    (h : Hyp151 D V₀ V L) (hV : IsElemAbelian 2 V) :
    ∃ ρ : ↥(Mbar D.M V₀ V hV) ≃* ↥(Mbar D.M (v1Sub D.M V₀ V hV L) V hV),
      ((lBar V₀ V hV L).subgroupOf (Mbar D.M V₀ V hV)).map ρ.toMonoidHom =
        (lStar D.M V₀ V hV L).subgroupOf (Mbar D.M (v1Sub D.M V₀ V hV L) V hV) ∧
      ∀ (g : ↥(Mbar D.M V₀ V hV)) (v : Vtil V₀ V hV),
        s15T7Kappa V₀ (v1Sub D.M V₀ V hV L) V hV (s15_Infra_le_v1Sub D.M V₀ V hV L)
            ((g : MulAut (Vtil V₀ V hV)) v) =
          ((ρ g : ↥(Mbar D.M (v1Sub D.M V₀ V hV L) V hV)) :
            MulAut (Vtil (v1Sub D.M V₀ V hV L) V hV))
            (s15T7Kappa V₀ (v1Sub D.M V₀ V hV L) V hV (s15_Infra_le_v1Sub D.M V₀ V hV L) v) := by
  obtain ⟨ρ, hcompat, hL⟩ := s16e_star_equiv D h1217 h hV
  refine ⟨ρ, hL, fun g v => ?_⟩
  obtain ⟨x, hxM, hgx⟩ := (mem_barSub V₀ V hV D.M (g : MulAut (Vtil V₀ V hV))).1 g.2
  have hs₁ : (x : G) ∈ stabTil (v1Sub D.M V₀ V hV L) V :=
    le_stabTil h.hyp125.pairFacts.le_normalizer
      (s15_Infra_le_normalizer_v1Sub h.hyp125 hV) hxM
  have hρg : ρ g = ⟨actTil (v1Sub D.M V₀ V hV L) V hV ⟨(x : G), hs₁⟩,
      actTil_mem_barSub (v1Sub D.M V₀ V hV L) V hV hxM hs₁⟩ := by
    have h1 := hcompat (x : G) hxM x.2 hs₁
    have h2 : g = ⟨actTil V₀ V hV ⟨(x : G), x.2⟩, actTil_mem_barSub V₀ V hV hxM x.2⟩ :=
      Subtype.ext hgx.symm
    rw [h2]
    exact h1
  rw [hρg, ← hgx]
  exact s15_T7_kappa_act V₀ _ V hV (s15_Infra_le_v1Sub D.M V₀ V hV L) x.2 hs₁ v

end Transport

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
