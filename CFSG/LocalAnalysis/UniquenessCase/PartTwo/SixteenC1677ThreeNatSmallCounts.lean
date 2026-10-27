module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1677ThreeDefs
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightKCtx
public import CFSG.Quasithin.AppendixH.H11.ModuleRank

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]
variable {D : Data G} {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}

theorem s168e3_false_of_sumOfNat_zero
    (c : S168e3Ctx D V₀ V L hV)
    {N : Subgroup (MulAut (Vtil V₀ V hV)) → Subgroup (Vtil V₀ V hV) →
      Subgroup (Vtil V₀ V hV) → Prop}
    (hcomp : CFSG.Open.IsComponentOf
      (lBar V₀ V hV L) (Mbar D.M V₀ V hV))
    (h0 : SumOfNat N (lBar V₀ V hV L)
      (wTil V₀ V hV L) (wTil V₀ V hV L ⊓ fixV (lBar V₀ V hV L)) 0) :
    False := by
  have hU : wTil V₀ V hV L = wTil V₀ V hV L ⊓ fixV (lBar V₀ V hV L) :=
    s16k_sumOfNat_zero h0
  have hle : wTil V₀ V hV L ≤ fixV (lBar V₀ V hV L) := by
    rw [hU]
    exact inf_le_right
  have hquad : IsQuadratic (lBar V₀ V hV L) := by
    rw [IsQuadratic, commV_eq_commSub]
    simpa [wTil, lBar] using hle
  have hEA : IsElemAbelian2 (lBar V₀ V hV L) :=
    CFSG.Quasithin.AppendixH.H11.isElemAbelian2_of_isQuadratic
      (s15_Infra_vtil_sq_eq_one V₀ V hV) hquad
  obtain ⟨a, ha, b, hb, hab⟩ :=
    CFSG.ComponentClassification.AS76b.Lemma34.exists_not_commute hcomp.2.2
  exact hab (hEA.1 a ha b hb)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
