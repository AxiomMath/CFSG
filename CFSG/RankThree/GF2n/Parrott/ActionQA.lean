module

public import CFSG.RankThree.GF2n.Parrott.LinearV
public import CFSG.RankThree.GF2n.Parrott.Setup

public section

namespace CFSG.RankThree.GF2n.Parrott

open CFSG CFSG.Open
open CFSG.ComponentClassification.CatFactsSmall.PSp43

open scoped Matrix

variable {G : Type} [Group G] [Finite G] {z : G}

@[expose] noncomputable def actionQA45 (h : Tim79a.ParrottHyp z)
    {hN : ((J z).subgroupOf (H z)).Normal} (D : QuotientData (z := z) hN) :
    QA45.originalSubgroup →* Matrix.GeneralLinearGroup (Fin 8) (ZMod 2) :=
  (actionGL (z := z) h).comp D.toQA45.symm.toMonoidHom

theorem actionQA45_apply (h : Tim79a.ParrottHyp z)
    {hN : ((J z).subgroupOf (H z)).Normal} (D : QuotientData (z := z) hN)
    (a : QA45.originalSubgroup) :
    actionQA45 (z := z) h D a = actionGL (z := z) h (D.toQA45.symm a) := rfl

end CFSG.RankThree.GF2n.Parrott
