module

public import CFSG.LocalAnalysis.UniquenessCase.UC6G.P6a
public import CFSG.LocalAnalysis.UniquenessCase.UC6P6b

public section

namespace CFSG.LocalAnalysis.UniquenessCase

open Subgroup CFSG.Open

namespace UC6G

open CFSG.Yardstones.Mf4cdcdf2e013 (TheoremCAt)
open CFSG.Blueprint (LieModel)
open CFSG.LocalAnalysis.UniquenessCase.UC22 (IsSpor IsAlt)
open CFSG.LocalAnalysis.UniquenessCase.UC6
open CFSG.LocalAnalysis.UniquenessCase.UC22 (Data)

namespace Mz614

variable {G : Type} [Group G] [Finite G] {Dat : Data G} (m : Mz614 Dat)

theorem list_of_L620_gt (hL : m.L620) (hr : 3 < m.r) :
    LieModel m.Lbar .PSL 2 m.r 2 ∨ (m.r = 5 ∧ (LieModel m.Lbar .Tits 0 2 1 ∨ IsAlt m.Lbar 10)) := by
  rcases hL.2 with h | ⟨h3, -⟩ | h
  · exact Or.inl h
  · omega
  · exact Or.inr h

theorem isSimpleGroup_L (hq : CFSG.Open.IsQuasisimple ↥m.L) (hcen : center ↥m.L = ⊥) :
    IsSimpleGroup ↥m.L := by
  have e : (↥m.L ⧸ center ↥m.L) ≃* ↥m.L :=
    (QuotientGroup.quotientMulEquivOfEq hcen).trans QuotientGroup.quotientBot
  exact e.isSimpleGroup_congr.mp hq.2

theorem hL3_of_kProjRep620 (hK : UCK.KProjRep620) (hL : m.L620) (hq : CFSG.Open.IsQuasisimple ↥m.L)
    (hr : 3 < m.r) : ∀ (q : ℕ), q.Prime → q ≠ m.r → ∀ (d : ℕ), d ≤ 6 →
      ∀ f : ↥m.L →* (Matrix.GeneralLinearGroup (Fin d) (ZMod q)) ⧸
        center (Matrix.GeneralLinearGroup (Fin d) (ZMod q)), f = 1 := by
  haveI := CFSG.pPrimeCore_normal (p := m.r) (G := ↥m.L)
  have h5 : 5 ≤ m.r := by
    by_contra h
    have h4 : m.r = 4 := by omega
    exact absurd m.hr (by rw [h4]; norm_num)
  intro q hq' hqr d hd f
  exact hK ↥m.L hq (CFSG.pPrimeCore m.r ↥m.L) (m.pPrimeCore_le_center_uc6 hq (m.r_dvd_card_L hL.1))
    m.r m.hr h5 (m.list_of_L620_gt hL hr) q hq' hqr d hd f

end Mz614

end UC6G

end CFSG.LocalAnalysis.UniquenessCase
