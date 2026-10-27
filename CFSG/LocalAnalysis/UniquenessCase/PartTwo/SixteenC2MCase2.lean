module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC2MSetting
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC2MInvFix
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC13BCFix3
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven10Case2LnIdent
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven10Case2LnModel

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

theorem s16c2m_case2_invFix (D : Data G) (h1217 : R1217 D) {V₀ V L : Subgroup G}
    (hV : IsElemAbelian 2 V) (hc : Counterex16 D V₀ V L hV) (hV0 : V₀ ≠ ⊥)
    (h2 : Case168_2 D V₀ V hV L) : s16n9bInvFix (Mbar D.M V₀ V hV) 3 3 := by
  obtain ⟨L₀, J₀, J₁, F, hLX, hKX, hKL, hK, hdir, hle, hE₀, hE₁, hfam⟩ :=
    s16c2m_setting D hc h2
  rcases hfam with ⟨n, hn5, -, -, -, hrk, hN₀, -⟩ | ⟨m, hm3, hm5, hL₀, hL, -, -, hsum⟩ |
    ⟨-, -, hrk, hN₀, -⟩ | ⟨-, -, hrk, hN₀, -⟩ | ⟨-, -, hrk, hN₀, -⟩
  · exact s16c2m_invFix_abs F hLX hKX hKL hK hdir hE₀ hE₁
      ⟨hrk, s16c13bc_fix3_alt hn5 hN₀⟩
  · have hcard : Nat.card ↥(lBar V₀ V hV L) = Nat.card ↥L₀ :=
      (SeitzReduction.LinearPilot.card_of_lieModel_PSL_two hL).trans
        (SeitzReduction.LinearPilot.card_of_lieModel_PSL_two hL₀).symm
    haveI : Finite (MulAut (Vtil V₀ V hV)) := MulEquiv.finite_left
    have hLeq : lBar V₀ V hV L = L₀ := Subgroup.eq_of_le_of_card_ge hle hcard.ge
    rw [← hLeq] at hdir
    have hT := s16c1610_isTensorS3L2_of_sum_natural hm3 hK hL hdir hsum
    intro φ _ _ _ z _ hz1
    exact s16c1610_tensor_exists_order_three_fix hm3 hT hz1
  · exact s16c2m_invFix_abs F hLX hKX hKL hK hdir hE₀ hE₁
      ⟨hrk, s16c13bc_fix3_sp (by norm_num) hN₀⟩
  · exact s16c2m_invFix_abs F hLX hKX hKL hK hdir hE₀ hE₁
      ⟨hrk, s16c13bc_fix3_omegaMinus (by norm_num) le_rfl hN₀⟩
  · exact s16c2m_invFix_abs F hLX hKX hKL hK hdir hE₀ hE₁
      ⟨hrk, s16c13bc_fix3_omegaMinus (by norm_num) le_rfl hN₀⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
