module

public import CFSG.Quasithin.H13.VolII16Restrict
public import CFSG.Quasithin.Background.B1MoreIrr
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Assembly.RankThreeEvenDefs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin Subgroup

@[expose] def S16C11V1ModelCover (D : FFModel) : Prop :=
  ∀ (W : Type) [CommGroup W] [Finite W], (∀ w : W, w ^ 2 = 1) →
    ∀ (H : Subgroup (MulAut W)) (Z : Subgroup W), Z ≤ fixV H → commV H = ⊤ →
      D.Realizes H ⊤ Z → Z = ⊥

theorem s16c11_v1_cover_restrict {D : FFModel} (hD : S16C11V1ModelCover D) {V : Type}
    [CommGroup V] [Finite V] (hV2 : ∀ v : V, v ^ 2 = 1) {L : Subgroup (MulAut V)}
    {U : Subgroup V} (hU : ∀ l ∈ L, ∀ u ∈ U, l u ∈ U) (hc : commSub U L = U)
    (h : D.Realizes L U (fixV L ⊓ U)) : fixV L ⊓ U = ⊥ := by
  have hcomm : XMod.commOf ↥L U = U := by rw [commOf_eq_commSub, hc]
  have h' := hD ↥U (CFSG.Quasithin.H13.VolI.sq_eq_one_of_subgroup hV2)
    (CFSG.Quasithin.H13.VolI.resHom L U hU).range ((fixV L ⊓ U).subgroupOf U)
    (CFSG.Quasithin.H13.VolI.subgroupOf_le_fixV_resHom_range hU inf_le_left)
    (CFSG.Quasithin.H13.VolI.commV_resHom_range hU hcomm)
    (CFSG.Quasithin.H13.VolI.realizes_resHom_range hU D h)
  rw [eq_bot_iff]
  intro z hz
  have hz' : (⟨z, hz.2⟩ : ↥U) ∈ (fixV L ⊓ U).subgroupOf U := mem_subgroupOf.2 hz
  rw [h', mem_bot] at hz'
  exact mem_bot.2 (congrArg Subtype.val hz')

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
