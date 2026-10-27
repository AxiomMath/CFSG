module

public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.RankThree.GF2n.Smith81.Sec220Defs

public section

namespace CFSG.RankThree.GF2n.Smith81

open CFSG CFSG.Open CFSG.CGT.Timmesfeld75 CFSG.RankThree.GF2n CFSG.RankThree.GF2n.Stroth80
open scoped commutatorElement Matrix

variable {G : Type} [Group G]

@[expose] def CStar (v : G) (V₁ : Subgroup G) : Subgroup ↥(Cv v) :=
  Subgroup.normalClosure ((V₁.subgroupOf (Cv v) : Subgroup ↥(Cv v)) : Set ↥(Cv v))

instance (v : G) (V₁ : Subgroup G) : (CStar v V₁).Normal := by
  unfold CStar
  infer_instance

end CFSG.RankThree.GF2n.Smith81
