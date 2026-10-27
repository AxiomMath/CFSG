module

public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Quasithin.Background.B1MoreIrr
public import CFSG.Quasithin.H13.VolII16Restrict

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin Subgroup

@[expose] def S16BoundCover (D : FFModel) (c : ℕ) : Prop :=
  ∀ (W : Type) [CommGroup W] [Finite W], (∀ w : W, w ^ 2 = 1) →
    ∀ (H : Subgroup (MulAut W)) (Z : Subgroup W), Z ≤ fixV H → commV H = ⊤ →
      D.Realizes H ⊤ Z → Nat.card ↥Z ≤ 2 ^ c

theorem s16fh_cover_restrict {D : FFModel} {c : ℕ} (hD : S16BoundCover D c) {V : Type}
    [CommGroup V] [Finite V] (hV2 : ∀ v : V, v ^ 2 = 1) {L : Subgroup (MulAut V)}
    {U Z : Subgroup V} (hU : ∀ l ∈ L, ∀ u ∈ U, l u ∈ U) (hc : commSub U L = U)
    (hZ : Z ≤ fixV L) (h : D.Realizes L U Z) : Nat.card ↥Z ≤ 2 ^ c := by
  have hcomm : XMod.commOf ↥L U = U := by rw [commOf_eq_commSub, hc]
  have hZU : Z ≤ U := by
    obtain ⟨π, hπ⟩ := h
    exact hπ.2.1
  have h' := hD ↥U (CFSG.Quasithin.H13.VolI.sq_eq_one_of_subgroup hV2)
    (CFSG.Quasithin.H13.VolI.resHom L U hU).range (Z.subgroupOf U)
    (CFSG.Quasithin.H13.VolI.subgroupOf_le_fixV_resHom_range hU hZ)
    (CFSG.Quasithin.H13.VolI.commV_resHom_range hU hcomm)
    (CFSG.Quasithin.H13.VolI.realizes_resHom_range hU D h)
  rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZU).toEquiv] at h'

end CFSG.LocalAnalysis.UniquenessCase.PartTwo

end
