module

public import CFSG.LocalAnalysis.UniquenessCase.UC6G.N588B5
public import CFSG.LocalAnalysis.UniquenessCase.UC6G.N588B6
public import CFSG.LocalAnalysis.UniquenessCase.UC6G.M591S
public import CFSG.LocalAnalysis.UniquenessCase.UC6P6a

public section

namespace CFSG.LocalAnalysis.UniquenessCase

open Subgroup CFSG.Open

namespace UC6G

open CFSG.Yardstones.Mf4cdcdf2e013 (TheoremCAt)
open CFSG.RankThree.PartOne.Census3 (IsoLie)
open CFSG.Blueprint (LieModel)
open CFSG.LocalAnalysis.UniquenessCase.UC22 (IsSpor IsAlt)
open CFSG.LocalAnalysis.UniquenessCase.UC6
open CFSG.LocalAnalysis.UniquenessCase.UC22 (Data)

namespace Mz614

variable {G : Type} [Group G] [Finite G] {Dat : Data G} (m : Mz614 Dat)

theorem pPrimeCore_le_center_uc6 (hq : CFSG.Open.IsQuasisimple ↥m.L) (hr : m.r ∣ Nat.card ↥m.L) :
    CFSG.pPrimeCore m.r ↥m.L ≤ center ↥m.L := by
  haveI : Fact m.r.Prime := ⟨m.hr⟩
  haveI := CFSG.pPrimeCore_normal (p := m.r) (G := ↥m.L)
  rcases normal_dichotomy_uc6 hq (CFSG.pPrimeCore m.r ↥m.L) with hc | htop
  · exact hc
  · exfalso
    have hcop : Nat.Coprime m.r (Nat.card (CFSG.pPrimeCore m.r ↥m.L)) :=
      CFSG.pPrimeCore_coprime_card
    rw [htop, Subgroup.card_top] at hcop
    exact m.hr.one_lt.ne' (Nat.Coprime.eq_one_of_dvd hcop hr)

theorem hmult_of_kMultList620 (hK : UCK.KMultList620) (hL : m.L620) (hq : CFSG.Open.IsQuasisimple ↥m.L)
    (hr : 3 < m.r) : Odd (Nat.card (center ↥m.L)) → center ↥m.L = ⊥ := by
  haveI := CFSG.pPrimeCore_normal (p := m.r) (G := ↥m.L)
  have h5 : 5 ≤ m.r := by
    by_contra h
    have h4 : m.r = 4 := by omega
    exact absurd m.hr (by rw [h4]; norm_num)
  have hlist : (∃ r : ℕ, r.Prime ∧ 5 ≤ r ∧ LieModel m.Lbar .PSL 2 r 2) ∨ LieModel m.Lbar .Tits 0 2 1 ∨
      IsAlt m.Lbar 10 := by
    rcases hL.2 with h | ⟨h3, -⟩ | ⟨-, h | h⟩
    · exact Or.inl ⟨m.r, m.hr, h5, h⟩
    · omega
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)
  exact hK ↥m.L hq (CFSG.pPrimeCore m.r ↥m.L) (m.pPrimeCore_le_center_uc6 hq (m.r_dvd_card_L hL.1)) hlist

noncomputable def equivLbar (h : CFSG.pPrimeCore m.r ↥m.L = ⊥) : ↥m.L ≃* m.Lbar :=
  haveI := CFSG.pPrimeCore_normal (p := m.r) (G := ↥m.L)
  (QuotientGroup.quotientBot (G := ↥m.L)).symm.trans (QuotientGroup.quotientMulEquivOfEq h.symm)

end Mz614

section TitsBridge


namespace Mz614

variable {G : Type} [Group G] [Finite G] {Dat : Data G} (m : Mz614 Dat)

theorem c623_of_list (hr : 3 < m.r) (hK322 : UCK.K322) (hK323 : UCK.K323)
    (hA10 : m.r = 5 → IsAlt ↥m.L 10 → m.C623) (h67 : R6_7 Dat)
    (h69 : R6_9 Dat) (h620 : m.C620) (hL : m.L620)
    (hOL : CFSG.pPrimeCore m.r ↥m.L = ⊥) : m.C623 := by
  have e := m.equivLbar hOL
  rcases hL.2 with hL2 | ⟨hr3, -⟩ | ⟨hr5, hT | hA⟩
  · exact Mz614.c623_of_L2 hK323 m h67 h69 h620 (CFSG.Blueprint.LieModel.of_mulEquiv e.symm hL2)
  · omega
  · exact Mz614.c623_of_tits hK322 m h67 h69 h620 hr5
      (isoLie_tits_of_lieModel (CFSG.Blueprint.LieModel.of_mulEquiv e.symm hT))
  · obtain ⟨f⟩ := hA
    exact hA10 hr5 ⟨e.trans f⟩

theorem c623_of_L620 (hr : 3 < m.r) (hK322 : UCK.K322) (hK323 : UCK.K323) (hMult : UCK.KMultList620)
    (hA10 : m.r = 5 → IsAlt ↥m.L 10 → m.C623) (h67 : R6_7 Dat)
    (h69 : R6_9 Dat) (h619 : m.C619) (hq : CFSG.Open.IsQuasisimple ↥m.L)
    (hL : m.L620) : m.C623 := by
  have hcen : center ↥m.L = ⊥ :=
    m.center_L_eq_bot h67 h619 (m.hmult_of_kMultList620 hMult hL hq hr)
  have hOL : CFSG.pPrimeCore m.r ↥m.L = ⊥ :=
    le_bot_iff.1 (hcen ▸ m.pPrimeCore_le_center_uc6 hq (m.r_dvd_card_L hL.1))
  exact m.c623_of_list hr hK322 hK323 hA10 h67 h69 hL.1 hL hOL

end Mz614

end TitsBridge

end UC6G

end CFSG.LocalAnalysis.UniquenessCase
