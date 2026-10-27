module

public import CFSG.LocalAnalysis.StandardType.GGTBJTwE6LeviSplit
public import CFSG.LocalAnalysis.StandardType.GGTBJTwE6LeviFoldCover
public import CFSG.LocalAnalysis.StandardType.GGTBJETypeCells
public import CFSG.LocalAnalysis.StandardType.GGTBJE6LeviIso
public import CFSG.LocalAnalysis.StandardType.GGTBJTwE6SplitCoverModel

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.LieType.AlgebraicGroups
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem ggTBJTwE6LeviK_foldCover
      (hRig : GGLabelRigidInput) : GGTBJTwE6LeviKFoldCover := by
  intro G _ _ p B Bs x L D J y K hH hJK hFact hinn hX n hΛ hK hreg labJ hΛJ hJlab hdvd hnc
  have hP : 5 < p ∧ p ∣ 2 ^ n - 1 ∧ 3 ∣ 2 ^ n + 1 := by
    by_contra h
    exact hnc (Or.inr h)
  obtain ⟨hp5, hpn, h3⟩ := hP
  have hp : p.Prime := hFact.out
  haveI : NeZero p := ⟨hp.ne_zero⟩
  have hp2 : p ≠ 2 := by omega
  have hn1 : 1 ≤ n := hΛ.1
  have hn2 : 2 ≤ n := by
    by_contra h
    have : n = 1 := by omega
    rw [this] at hpn
    have h1 : p ∣ 1 := by simpa using hpn
    exact hp.ne_one (Nat.dvd_one.mp h1)
  refine ggTBJE6LeviK_of_cellFn hH hJK
    fun hBs hSC hJK' hxBs hJg hgX hcomp bX hbX1 hbXc hcardJ => ?_
  obtain ⟨hN, F, _, _, σ, hcard, hσ, ζ, hζ, hζσ, π, hπs, hπk, hZR, hZp, hζo, hA⟩ :=
    ggTwE6Split_coverModel_K hRig hH hΛ hK hp5 hpn h3
  exact ggTBJF4Levi_of_cover_frame hp2 hBs hSC hN hJK' hxBs hJg hgX hcomp hZp hZR π hπs hπk hA
    (twE6Split_leviFrame σ hn2 hcard hσ hp2 hpn hζo hζ hζσ) bX hbX1 hbXc hcardJ

end CFSG.StandardType

end
