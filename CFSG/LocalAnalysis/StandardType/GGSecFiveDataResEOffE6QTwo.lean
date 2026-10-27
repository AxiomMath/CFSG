module

public import CFSG.LocalAnalysis.StandardType.GGSecFivePhanEData
public import CFSG.LocalAnalysis.StandardType.GGSecFiveWeylE6QTwoDefs
public import CFSG.LocalAnalysis.StandardType.GGSecFiveWeylE6QTwoRowE
public import CFSG.LocalAnalysis.StandardType.GGFrameRouteJoin
public import CFSG.LocalAnalysis.StandardType.GGSecFivePhanRankOneSix
import CFSG.LocalAnalysis.StandardType.GGSecFiveRankOneCard

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.Blueprint CFSG.LieType.Universal
  CFSG.ClassicalInvolution.Phan

theorem ggSecFiveDataResEOffE6QTwo_of_phanE
    (hPE : PhanEInput2) (hL1 : GGSecFiveL1PhanInput) (hRk1 : GGSecFiveRk1PhanInput)
    (hGen : GGSecFiveGenPhanInput) (hOrb : GGSecFiveOrbPhanInput) (hL2 : GGSecFiveL2PhanInput)
    (hPair : GGSecFivePhanPairInput) (hNbr : GGSecFiveNonSplitNbrInput)
    (hJ : GGSecFiveJoinPhanEInput) (h78 : GGSecFiveDataResPhanE78QTwoInput) :
    GGSecFiveDataResEOffE6QTwoInput := by
  intro G _ _ p B Bs x L D J 𝒦 hcfg hNotReg ι M e hpres hE hC
  by_cases hs : GGSplitLie p L
  · exact absurd ⟨𝒦, hcfg, hs, ι, M, e, hpres, Or.inr hE⟩ hNotReg
  by_cases h6 : ∃ r ∈ ggAutomizer L Bs, r ∈ ggCoxRefl M e ∧ Nat.card (ggRankOneIn L Bs r) = 6
  · rcases hE with h6' | h78'
    · exact absurd ⟨𝒦, hcfg, hs, ι, M, e, hpres, h6', h6⟩ hC
    · exact h78 G p B Bs x L D J 𝒦 hcfg hNotReg hs ι M e hpres h78' h6
  exact ggSecFiveData_phanE_of_big hPE hL1 hRk1 hGen hOrb hL2 hPair hNbr hJ hcfg hs hpres hE
    (fun r hrA hrC h => h6 ⟨r, hrA, hrC, h⟩)

theorem ggSecFiveDataResPhanE78QTwoInput_of_frameRouteJoin
    (hI : FrameRoute.GGFrameRouteJoinInputs) (hTBF : GGTBFixInput) (hWI : GGNbrInnerWeylInput)
    (hRk1 : GGSecFiveRk1PhanInput) (hLab : GGSecFiveE78QTwoLabelInput) :
    GGSecFiveDataResPhanE78QTwoInput := by
  intro G _ _ p B Bs x L D J 𝒦 hcfg _ hs ι M e hP hE h6
  have hp3 : p = 3 := by
    obtain ⟨r, hrA, hrC, hr6⟩ := h6
    exact (ggSecFivePhanRankOne_of_card_six hRk1 hcfg hs hP (GGIsWeylMatrixE.le_three (Or.inr hE))
      (Or.inl rfl) hrA hrC hr6).1
  have hq : GGInnerDiagOnLabel GGLabQTwo p Bs L := by
    obtain ⟨hperf, lab, hΛ, hraw⟩ := hcfg.1.2.2.1.1
    have hlab : GGHasLabel lab (↥L ⧸ Subgroup.center ↥L) :=
      largeEvenRawDatum_mono (fun _ _ _ _ ⟨_, _, θ, _⟩ => ⟨θ⟩) hraw
    exact ⟨hperf, lab, hΛ, largeEvenRawDatum_mono (fun _ _ _ _ ⟨hsimp, hna, θ, hθ⟩ =>
      ⟨hsimp, hna, θ, hLab G p B Bs x L D J 𝒦 hcfg hs hp3 ι M e hP hE h6 lab hΛ hlab, hθ⟩) hraw⟩
  have hJoin : ∀ {ι' : Type} (M' : CoxeterMatrix ι') (e' : ι' ≃ ι), M = M'.reindex e' →
      FrameRoute.GGSecFiveWeylAtJoin p B Bs x L D J M' := by
    intro ι' M' e' hMeq
    subst hMeq
    by_cases h𝒦 : 𝒦.Nonempty
    · exact ⟨𝒦, hcfg.2.2.2.1, h𝒦,
        GGWeylOfType.of_reindex (M := M') (e := e') (A := ggAutomizerJoin L Bs 𝒦) ⟨e, hP.2⟩⟩
    · rw [Finset.not_nonempty_iff_eq_empty] at h𝒦
      subst h𝒦
      exact (hcfg.weylAt_of_card_le_one (by simp) e hP).of_reindex.toJoin
  rcases hE with ⟨e', hMeq⟩ | ⟨e', hMeq⟩
  · exact FrameRoute.ggSecFiveData_of_frameRouteJoin hI hTBF hWI p B Bs x L D J hcfg.1 hcfg.2.1 hq
      (Or.inl (hJoin _ e' hMeq))
  · exact FrameRoute.ggSecFiveData_of_frameRouteJoin hI hTBF hWI p B Bs x L D J hcfg.1 hcfg.2.1 hq
      (Or.inr (hJoin _ e' hMeq))

theorem ggSecFiveE78QTwoLabelInput_of_rk1
    (hRk1 : GGSecFiveRk1PhanInput) :
    GGSecFiveE78QTwoLabelInput := by
  intro G _ _ p B Bs x L D J 𝒦 hcfg hns _ ι M e hP hE h6 lab hΛ hlab
  obtain ⟨r, hrA, hrC, hr6⟩ := h6
  obtain ⟨F, hF, hFfin, θ, -, hθinj, hθrange, -, -, -, hlabF⟩ :=
    hRk1 G p B Bs x L D J 𝒦 hcfg hns ι M e hP (GGIsWeylMatrixE.le_three (Or.inr hE)) L
      (Or.inl rfl) r hrA hrC
  letI : Field F := hF
  haveI : Finite F := hFfin
  have hcardSL : Nat.card (ggRankOneIn L Bs r) =
      Nat.card (Matrix.SpecialLinearGroup (Fin 2) F) := by
    rw [← hθrange]
    exact Nat.card_congr (MonoidHom.ofInjective hθinj).toEquiv.symm
  rw [hcardSL, ggSL2_card F] at hr6
  have hq2 : 2 ≤ Nat.card F := Finite.one_lt_card
  have hF2 : Nat.card F = 2 := by
    by_contra hne
    have h3 : 3 ≤ Nat.card F := by omega
    have h9 : 9 ≤ Nat.card F ^ 2 := by simpa using Nat.pow_le_pow_left h3 2
    have h24 : 3 * 8 ≤ Nat.card F * (Nat.card F ^ 2 - 1) := Nat.mul_le_mul h3 (by omega)
    omega
  have hn : 2 ^ lab.n ≤ 2 := hF2 ▸ hlabF lab hΛ hlab
  by_contra hge
  have h4 : 4 ≤ 2 ^ lab.n :=
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ lab.n := Nat.pow_le_pow_right (by norm_num) (by omega)
  omega

theorem ggSecFiveDataResEOffE6QTwoInput_of_frameRouteJoin
    (hPE : PhanEInput2) (hL1 : GGSecFiveL1PhanInput) (hRk1 : GGSecFiveRk1PhanInput)
    (hGen : GGSecFiveGenPhanInput) (hOrb : GGSecFiveOrbPhanInput) (hL2 : GGSecFiveL2PhanInput)
    (hPair : GGSecFivePhanPairInput) (hNbr : GGSecFiveNonSplitNbrInput)
    (hJ : GGSecFiveJoinPhanEInput) (hI : FrameRoute.GGFrameRouteJoinInputs)
    (hTBF : GGTBFixInput) (hWI : GGNbrInnerWeylInput) (hLab : GGSecFiveE78QTwoLabelInput) :
    GGSecFiveDataResEOffE6QTwoInput :=
  ggSecFiveDataResEOffE6QTwo_of_phanE hPE hL1 hRk1 hGen hOrb hL2 hPair hNbr hJ
    (ggSecFiveDataResPhanE78QTwoInput_of_frameRouteJoin hI hTBF hWI hRk1 hLab)

end CFSG.StandardType

end
