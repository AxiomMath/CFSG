module

public import CFSG.RankThree.GF2n.Stroth80.HeringSec93AC4
public import CFSG.RankThree.GF2n.Stroth80.HeringSec93N
public import CFSG.RankThree.GF2n.Stroth80.HeringSec93XH
public import CFSG.RankThree.GF2n.Stroth80.HeringSec93TF
public import CFSG.RankThree.GF2n.Stroth80.HeringSec93TA
public import CFSG.RankThree.GF2n.Stroth80.HeringSec93TMain
public import CFSG.RankThree.GF2n.Stroth80.CarterSec93AltStep3
public import CFSG.CGT.Timmesfeld75.L2Defs
public import CFSG.RankThree.GF2n.Stroth80.HeringSec9RThree
public import CFSG.Open.Catalog
public import CFSG.RankThree.GF2n.Tim77Prop24
public import CFSG.RankThree.GF2n.Tim77Prop24Inv
public import CFSG.CGT.T75N.BenderCenter
public import CFSG.CGT.T75N.UnitaryTwoGen
public import CFSG.CGT.T75N.OddCycBender
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.GroupTheory.DedekindNormalizer
public import CFSG.RankThree.GF2n.Stroth80.Core4Frame
public import CFSG.RankThree.GF2n.Stroth80.Core4StepB
public import CFSG.RankThree.GF2n.Stroth80.HeringSec94ConjV
public import CFSG.RankThree.GF2n.Stroth80.HeringSec9ROneSL
public import CFSG.RankThree.GF2n.Stroth80.Sec97Conn

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
  CFSG.RankThree.GF2n.Smith81
open scoped commutatorElement Matrix

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

namespace HS9

theorem step93L2AltXH_of_cfg (h34 : Stroth34Statement) (h311a : Stroth311aStatement)
    (h311bComm : Stroth311bCommStatement) (h312b : Stroth312bStatement)
    (hX : Classify.TheoremXStatement) {hc : Ctx M Q Z B} {n : ℕ} {t r : G} {Z0 : Subgroup G}
    {h : G} (cfg : Cfg93c hc n t r Z0 h)
    (hq : QuotSat (Xhat M Q B h) (Fhat M Q B h) (IsSLModel 2 (Nat.card Z))) :
    LB M Q B ⊓ hc.CN t ≤ Fhat M Q B h ∨
      LB M Q B ⊓ conjSubgroup h (LB M Q B) ⊔ (LB M Q B ⊓ hc.CN t) = LB M Q B :=
  step93L2AltXH_of_near h34 h311a h311bComm h312b cfg hq (conjB_le_QB_of_L2 h34 h311a hX cfg hq)

end HS9

theorem step93L2AltXHStatement_of_inputs (h34 : Stroth34Statement)
    (h311a : Stroth311aStatement) (h311bComm : Stroth311bCommStatement)
    (h312b : Stroth312bStatement) (hX : Classify.TheoremXStatement) :
    Step93L2AltXHStatement := by
  intro G _ _ M Q Z B hc n t r Z0 h cfg hq
  exact HS9.step93L2AltXH_of_cfg h34 h311a h311bComm h312b hX cfg hq

end CFSG.RankThree.GF2n.Stroth80
