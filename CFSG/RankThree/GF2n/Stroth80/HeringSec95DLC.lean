module

public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma54
public import CFSG.LocalAnalysis.AGLEmbedding.SeitzEqTwo.DescentE
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.Quasithin.Vol2.Ch10SecKGA318
public import CFSG.RankThree.GF2n.Stroth80.HeringSec95CStmt
public import CFSG.RankThree.PartTwo.KFacts.KS21Mult
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank CFSG.RankThree.GF2n
open scoped commutatorElement Matrix

namespace HS9

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

theorem exists_gen_Vt95 {hc : Ctx M Q Z B} {t : G} {Z0 : Subgroup G} (hcen : Centre95 hc t Z0) :
    ∃ s ∈ Z0, ⁅Q, Subgroup.zpowers s⁆ ⊔ Z = Vt M (LB M Q B) B Z t := by
  obtain ⟨s0, hs0, hs0Q⟩ : ∃ s ∈ Z0, s ∉ Q := by
    by_contra hall
    push Not at hall
    have h1 : Q.relIndex Z0 = 1 := Subgroup.relIndex_eq_one.mpr hall
    have h2 := hcen.2.1
    have h3 := hc.hyp.q4
    rw [h1] at h2
    omega
  exact ⟨s0, hs0, hcen.2.2 s0 hs0 hs0Q⟩

end HS9

end CFSG.RankThree.GF2n.Stroth80
