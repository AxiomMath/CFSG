module

public import CFSG.LocalAnalysis.UniquenessCase.UC6K316Small
public import CFSG.LocalAnalysis.UniquenessCase.UC6K316Tits3
public import CFSG.LocalAnalysis.UniquenessCase.UC6K316U42
public import CFSG.LocalAnalysis.UniquenessCase.UC6K316L34

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UCK

open CFSG.Open Subgroup

namespace Hyp36

variable {G : Type} [Group G] [Finite G] {M E : Subgroup G} {p : ℕ}


theorem concl_of_lieEven (hS : AGLEmbeddingD2.KFactSeitzRankTwo) (h : Hyp36 G M p E) {L : Subgroup G}
    [L.Normal] (hL : CFSG.IsComponent L) (hLM : L ⊔ M = ⊤) (hne : ⁅L, pCoreOf 2 M⁆ ≠ ⊥)
    (d : TauCeti.ValidLieTypeIndex) (φ : ↥L ⧸ Subgroup.center ↥L ≃* (TauCeti.CFSGIndex.lie d).Group)
    (hd : d.1.characteristic = 2) : K36Concl M p := by
  by_cases hex : AGLEmbeddingD2.IsD2SeitzException p d.1
  · rcases hex with ⟨rfl, h1 | h2 | h3 | h4 | h5⟩ | ⟨rfl, h6 | h7⟩
    · exact (h.false_of_twoSigTriv hL hne (MulEquiv.refl _) (twoSigTriv_l28 d h1 φ)).elim
    · exact h.concl_of_l34 rfl hL hLM hne d h2 φ
    · exact (h.false_of_twoSigTriv hL hne (MulEquiv.refl _) (twoSigTriv_u42 d h3 φ)).elim
    · exact (h.false_of_twoSigTriv hL hne (MulEquiv.refl _) (twoSigTriv_sp d h4 φ)).elim
    · exact (h.false_of_twoSigTriv hL hne (MulEquiv.refl _) (twoSigTriv_tits_three d h5 φ)).elim
    · exact (h.false_of_twoSigTriv hL hne (MulEquiv.refl _) (twoSigTriv_tits_five d h6 φ)).elim
    · exact (h.false_of_twoSigTriv hL hne (MulEquiv.refl _) (twoSigTriv_sz32 d h7 φ)).elim
  · exact (h.false_of_seitz hS hL hne d φ (by rw [hd]; exact h.odd) hex).elim

end Hyp36

end CFSG.LocalAnalysis.UniquenessCase.UCK
