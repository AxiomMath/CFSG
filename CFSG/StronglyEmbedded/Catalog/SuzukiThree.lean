module

public import CFSG.StronglyEmbedded.Catalog.Suzuki
import CFSG.StronglyEmbedded.MatrixGroups.SzModel
import CFSG.Models.BenderSuzuki
import CFSG.Quasithin.Background.ONanE68RankOneSz

public section

namespace CFSG.BenderSuzuki.Catalog

theorem not_three_dvd_card_lie_suzuki {k : ℕ} (hk : (TauCeti.LieTypeIndex.suzuki k).Valid) :
    ¬ 3 ∣ Nat.card (TauCeti.CFSGIndex.lie ⟨.suzuki k, hk⟩).Group := by
  have hk1 : 1 ≤ k :=
    (TauCeti.LieTypeIndex.inStandardRange_iff _).1 ((TauCeti.LieTypeIndex.valid_iff _).1 hk).1
  let φ : (TauCeti.CFSGIndex.lie ⟨.suzuki k, hk⟩).Group ≃* CFSG.Open.Sz k :=
    (groupEquivSuzukiMatrixGroup hk).trans
      (MulEquiv.subgroupCongr ((CFSG.BenderSuzuki.szModel_eq_suzukiMatrixGroup k).symm.trans
        (CFSG.Models.benderSzModel_eq_sz k)))
  rw [Nat.card_congr φ.toEquiv]
  exact CFSG.Quasithin.E6.E68Proof.RankOne.not_three_dvd_card_sz hk1

end CFSG.BenderSuzuki.Catalog

end
