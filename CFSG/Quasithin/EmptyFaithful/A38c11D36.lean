module

public import CFSG.Quasithin.Background.F918P2
public import CFSG.Quasithin.Background.B1MoreIrr

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique

@[expose] def D36B48qN : Prop :=
  ∀ (W : Type) [CommGroup W] [Finite W] (M Mp T L : Subgroup (MulAut W)) (V : Subgroup W)
    (t : MulAut W), D3Std M Mp T L V → V < orbSup T V → t ∈ T →
    t ∉ Subgroup.normalizer (L : Set (MulAut W)) → Mp = L ⊔ conjAutSub t L →
    D36cConcl Mp T L V t →
    qOf (autSub (Mp ⊔ T) (orbSup T V)) ≤ ((2 : ℚ) : WithTop ℚ) →
    IsPSL 3 2 1 ↥(autSub L (orbSup T V)) →
    (∃ s ∈ T, s ∈ Subgroup.normalizer (L : Set (MulAut W)) ∧ s ∉ stabSub V) →
    V ⊓ fixV Mp = ⊥

theorem d36B48q_of_narrow (hc : D36c) (hN : D36B48qN) : D36B48q := by
  intro W _ _ M Mp T L V t std hlt ht htn hMp h0 hq hpsl hs
  rcases hc W M Mp T L V std hlt t ht htn hMp with hc1 | hc2
  · exact hN W M Mp T L V t std hlt ht htn hMp hc1 hq hpsl hs
  · exfalso
    have hL : ∀ v ∈ V, ∀ g ∈ L, g v = v := fun v hv g hg =>
      hc2.1 v hv g (by rw [conjAutSub_inv_conjAutSub]; exact hg)
    have hMpfix : V ≤ fixV Mp := by
      intro v hv x hx
      rw [hMp] at hx
      have hstab : L ⊔ conjAutSub t L ≤ MulAction.stabilizer (MulAut W) v := by
        refine sup_le (fun g hg => ?_) (fun g hg => ?_)
        · exact MulAction.mem_stabilizer_iff.mpr (hL v hv g hg)
        · exact MulAction.mem_stabilizer_iff.mpr (h0 v hv g hg)
      exact MulAction.mem_stabilizer_iff.mp (hstab hx)
    have hcomm : commSub V Mp = V := by
      rw [← commOf_eq_commSub]
      exact std.hyp.irr.2.2.1
    have hV : V = ⊥ := by
      rw [← hcomm]
      exact commSub_eq_bot_iff.mpr hMpfix
    subst hV
    simp [orbSup] at hlt

end CFSG.Quasithin
