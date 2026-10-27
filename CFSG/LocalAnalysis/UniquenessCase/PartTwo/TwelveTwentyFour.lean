module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs12c3
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.TwelveSeventeen
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenKbar

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

namespace TwelveTwentyFour

theorem ne_bot_of_isComponentOf {A : Type*} [Group A] {L X : Subgroup A}
    (hL : IsComponentOf L X) : L ≠ ⊥ := by
  intro h0
  obtain ⟨-, -, -, hs⟩ := hL
  obtain ⟨a, b, hab⟩ := hs.toNontrivial.exists_pair_ne
  induction a using QuotientGroup.induction_on with
  | H a =>
    induction b using QuotientGroup.induction_on with
    | H b =>
      apply hab
      have ha : a = 1 := Subtype.ext (Subgroup.mem_bot.1 (h0 ▸ a.2))
      have hb : b = 1 := Subtype.ext (Subgroup.mem_bot.1 (h0 ▸ b.2))
      rw [ha, hb]

end TwelveTwentyFour

theorem twelve_twentyFour (D : Data G) (hx : DataExt D) (h61 : UC6.R6_1 D) (h127 : R127 D)
    (h1214 : F12.R1214 D) (h4128 : W4Lem12_8) {V₀ V : Subgroup G} (h : Hyp125 D V₀ V)
    {L H : Subgroup (MulAut (Vtil V₀ V h.isElemAbelian))}
    (hL : L ∈ compBar D.M V₀ V h.isElemAbelian)
    (hH : H = ⨆ X ∈ conjSet L (Mbar D.M V₀ V h.isElemAbelian), X) :
    dMinDeg ↥L ≤ mBar D.M V₀ V h.isElemAbelian ∨
      (IsDirSumOver (conjSet L (Mbar D.M V₀ V h.isElemAbelian))
          (fun X => commV (autQuot X (fixV H))) ∧
        ∃ I ∈ irrSet L,
          (E3.mParam (autSub (autQuot (Mbar D.M V₀ V h.isElemAbelian) (fixV H))
              (I.map (QuotientGroup.mk' (fixV H)))) : ℚ) *
              ((rk ↥(commV (autQuot L (fixV H))) : ℚ) /
                (rk ↥(I.map (QuotientGroup.mk' (fixV H))) : ℚ)) ≤
            mBar D.M V₀ V h.isElemAbelian) ∨
      ∃ (Y : Subgroup (MulAut (Vtil V₀ V h.isElemAbelian))) (e : ℕ),
        Y ≤ Mbar D.M V₀ V h.isElemAbelian ∧
        IsDirSumOver (conjSet Y (Mbar D.M V₀ V h.isElemAbelian)) commV ∧
        CFSG.Open.IsSubnormal L Y ∧ IsNaturalO4Plus Y e ∧ mBar D.M V₀ V h.isElemAbelian = e := by
  have hM1 : Mbar D.M V₀ V h.isElemAbelian ≠ ⊥ := fun hb =>
    TwelveTwentyFour.ne_bot_of_isComponentOf hL (le_bot_iff.1 (hb ▸ hL.1))
  rcases h4128 (Vtil V₀ V h.isElemAbelian) (s15_Infra_vtil_sq_eq_one V₀ V h.isElemAbelian)
      (Mbar D.M V₀ V h.isElemAbelian)
      (fun _ hP hN h2 => s15_Kbar_eq_bot_of_normal_isPGroup D h hP hN h2)
      (TwelveSeventeen.isBasicModule D hx h61 h127 h1214 h hM1) L hL H hH with
    h1 | h2 | ⟨Y, e, hY, hsum, hsn, hnat, hm, -⟩
  · exact Or.inl h1
  · exact Or.inr (Or.inl h2)
  · exact Or.inr (Or.inr ⟨Y, e, hY, hsum, hsn, hnat, hm⟩)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
