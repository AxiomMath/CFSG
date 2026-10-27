module

public import CFSG.LocalAnalysis.UniquenessCase.UC6P6a

public section

namespace CFSG.LocalAnalysis.UniquenessCase

open Subgroup CFSG.Open

namespace UCK

@[expose] def KProjRep620 : Prop :=
  ∀ (J : Type) [Group J] [Finite J], CFSG.Open.IsQuasisimple J →
    ∀ (N : Subgroup J) [N.Normal], N ≤ center J → ∀ r : ℕ, r.Prime → 5 ≤ r →
      (CFSG.Blueprint.LieModel (J ⧸ N) .PSL 2 r 2 ∨
        (r = 5 ∧ (CFSG.Blueprint.LieModel (J ⧸ N) .Tits 0 2 1 ∨
          CFSG.LocalAnalysis.UniquenessCase.UC22.IsAlt (J ⧸ N) 10))) →
      ∀ q : ℕ, q.Prime → q ≠ r → ∀ d : ℕ, d ≤ 6 →
        ∀ f : J →* (Matrix.GeneralLinearGroup (Fin d) (ZMod q)) ⧸
          center (Matrix.GeneralLinearGroup (Fin d) (ZMod q)), f = 1

end UCK

namespace UC6

open CFSG.Yardstones.Mf4cdcdf2e013 (Standing4 Setup4 TheoremCAt Theorem614Four)
open CFSG.Blueprint (LieModel)
open CFSG.LocalAnalysis.UniquenessCase.UC22 (IsSpor IsAlt)

namespace Mz614

variable {G : Type} [Group G] [Finite G] (m : Mz614 G)

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

end UC6

end CFSG.LocalAnalysis.UniquenessCase
