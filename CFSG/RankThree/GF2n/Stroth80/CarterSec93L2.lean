module

public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma54
public import CFSG.LocalAnalysis.AGLEmbedding.SeitzEqTwo.DescentE
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.Quasithin.Vol2.Ch10SecKGA318
public import CFSG.RankThree.GF2n.Stroth80.Sec34TI
public import CFSG.RankThree.GF2n.Stroth80.Sec7Basic
public import CFSG.RankThree.GF2n.Stroth80.Sec9Defs
public import CFSG.RankThree.PartTwo.KFacts.KS21Mult
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement Matrix

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

theorem step93L2_comm_B (hc : Ctx M Q Z B) {h : G} (hh : h ∈ M)
    (hK : LB M Q B ⊓ conjSubgroup h (LB M Q B) ≠ Q) :
    ∀ x ∈ conjSubgroup h B, ∀ y ∈ B, x * y = y * x := by
  by_contra hcon
  push Not at hcon
  exact hK (hc.LB_inf_conj_eq_Q hh hcon)

theorem step93L2_false_of_le_H (hc : Ctx M Q Z B) {n : ℕ} {t : G} (hs : Sec9Hyp hc n t)
    {Z0 : Subgroup G} (hZ0 : IsCentrePre Z0 (Rt M (LB M Q B) t) Q)
    {H : Subgroup G} (hZH : Z0 ≤ H) (hZQ : Z0 ⊓ H = Q) : False := by
  have htZ : t ∈ Z0 := IsCentrePre.mem_of_mem_LB (hc := hc) hs.mem hZ0
  have htH : t ∈ H := hZH htZ
  have htQ : t ∈ Q := by
    have : t ∈ Z0 ⊓ H := Subgroup.mem_inf.mpr ⟨htZ, htH⟩
    rwa [hZQ] at this
  exact hs.notQ htQ

end CFSG.RankThree.GF2n.Stroth80
