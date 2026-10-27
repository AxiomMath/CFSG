module

public import CFSG.RankThree.PartTwo.Sec21.FF84S410DataB
public import CFSG.RankThree.PartTwo.Sec21.FF84S410Omega

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF84.S4

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

open CFSG CFSG.RankThree.PartTwo.Sec21 CFSG.RankThree.PartTwo.Sec21.FF84
open CFSG.ComponentClassification.AS81 CFSG.ComponentClassification.AS81.Sec2Omega
open CFSG.Assembly.LowTwoRank (StatedClassicalModel)

variable {G : Type} [Group G] [Finite G]

theorem S410_data (h48 : FF84_4_8) (h47 : FF84_4_7)
    (hCSb : HypS48CSb) (hb2 : HypS48b2) (h49 : HypS49orbits) (h49S6 : HypS49S6)
    (hE27 : HypOmNormalizerE27) (hPar : HypOmParabolic) (hPair : HypOmPair)
    {b : G} {L B K : Subgroup G} {b₁ b₂ : G} (h : FF84Post b L B K b₁ b₂) {U : Subgroup G}
    (hU : U ∈ PiStar (Cen b) B 2) : ∃ s t : G, FF84MData b (Op 2 (Nor U)) s t := by
  obtain ⟨e, hfor, s, t, hs, ht, hes, het⟩ :=
    S410_omega_pair h48 h47 hCSb hb2 h49 h49S6 hE27 h hU
  obtain ⟨ψ, H⟩ := exists_omSet hfor
  have hgen : B = Subgroup.closure {b, b₁, b₂} := h.sec.mono.2.1
  have hbB : b ∈ B := by rw [hgen]; exact Subgroup.subset_closure (by simp)
  have hBS : B ≤ Nor (Op 2 (Nor U)) := hU.2.2.1.trans (le_nor_op2 (Nor U))
  obtain ⟨hs1, ht1, hst, hSs, hSt, hSst⟩ := data_basic H hes het
  obtain ⟨hrel, hQ17⟩ := data_B H het hPar hPair
  refine ⟨s.1, t.1, hBS hbB, s.2, t.2, hs1, ht1, hst,
    Subgroup.mem_centralizer_singleton_iff.2 (Subgroup.mem_centralizer_singleton_iff.1 hs).symm,
    Subgroup.mem_centralizer_singleton_iff.2 (Subgroup.mem_centralizer_singleton_iff.1 ht).symm,
    hSs, hSt, hSst, M_le_nor H hes het, ?_, data_CM H hes het,
    fun W hTW hWS hM => data_max H hes het W hTW hWS hM, hrel, hQ17⟩
  obtain ⟨eA0⟩ := hPair qMinus_sig0 qMinus_tau0 qMinus_sig0_add_tau0 tau0_ne_zero
  have eA : ↥P2 ≃* alternatingGroup (Fin 5) := eA0
  exact ⟨↥P2, inferInstance, phiM H hes het,
    CFSG.QuasithinUnique.Ch1.statedClassicalModel_psl_two_four_of_alternating_five _ ⟨eA⟩,
    phiM_surj H hes het, phiM_ker H hes het⟩

theorem ff84_4_10m_of (h43 : FF84_4_3) (h44 : FF84_4_4)
    (h46 : FF84_4_6) (h47 : FF84_4_7) (h48 : FF84_4_8) (hCSb : HypS48CSb) (hb2 : HypS48b2)
    (h49 : HypS49orbits) (h49S6 : HypS49S6) (hE27 : HypOmNormalizerE27)
    (hPar : HypOmParabolic) (hPair : HypOmPair) : FF84_4_10m := by
  intro G _ _ b L B K b₁ b₂ hsec U hU
  exact S410_data h48 h47 hCSb hb2 h49 h49S6 hE27 hPar hPair
    (post_of_items h43 h44 h46 hsec) hU

end CFSG.RankThree.PartTwo.Sec21.FF84.S4

end
