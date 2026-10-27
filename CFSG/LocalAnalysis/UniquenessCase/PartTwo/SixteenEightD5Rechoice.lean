module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Sixteen4136Input
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Sixteen4136Lift

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

theorem s16e_d5_rechoice (D : Data G) {V₀ V : Subgroup G} (hV : IsElemAbelian 2 V)
    (h16 : Hyp16 D V₀ V) {t : MulAut (Vtil V₀ V hV)} (ht : t ∈ Mbar D.M V₀ V hV)
    (ht2 : t ^ 2 = 1) (ht1 : t ≠ 1) (htr : rk ↥(commSub ⊤ (Subgroup.zpowers t)) ≤ 3)
    {K : Subgroup (MulAut (Vtil V₀ V hV))} (hK : Conc4_136W (Mbar D.M V₀ V hV) t K) :
    ∃ L' : Subgroup G, Setting16 D V₀ V L' ∧ barSub V₀ V hV L' = K ∧
      Conc4_136 D V₀ V hV L' ∧
      s15 D.M V₀ V hV L' =
        Set.ncard {X : Subgroup (MulAut (Vtil V₀ V hV)) |
          ∃ φ ∈ Mbar D.M V₀ V hV, X = K.map (MulAut.conj φ).toMonoidHom} := by
  have hMs : D.M ≤ stabTil V₀ V :=
    le_stabTil h16.hyp125.pairFacts.le_normalizer h16.hyp125.pairFacts.le_normalizer₀
  have hKle : K ≤ Mbar D.M V₀ V hV := hK.le
  have hbar : barSub V₀ V hV (liftO2 D.M V₀ V hV K) = K :=
    barSub_liftO2 hV hMs hKle hK.twoResidual_eq
  have h151 : Hyp151 D V₀ V (liftO2 D.M V₀ V hV K) :=
    hyp151_liftO2 D h16.hyp125 hKle hK.twoResidual_eq hK.fstar_eq hK.2.1
  refine ⟨liftO2 D.M V₀ V hV K, ⟨h16, h151⟩, hbar, ⟨t, ht, ht2, ht1, htr, ?_⟩, ?_⟩
  · have : lBar V₀ V hV (liftO2 D.M V₀ V hV K) = K := hbar
    rw [this]
    exact hK
  · show Set.ncard {X : Subgroup (MulAut (Vtil V₀ V hV)) |
      ∃ φ ∈ Mbar D.M V₀ V hV,
        X = (barSub V₀ V hV (liftO2 D.M V₀ V hV K)).map (MulAut.conj φ).toMonoidHom} = _
    rw [hbar]

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
