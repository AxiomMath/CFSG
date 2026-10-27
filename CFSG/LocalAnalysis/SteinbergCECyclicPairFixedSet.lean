module

public import Mathlib.Data.Nat.Totient
public import Mathlib.Data.Sym.Sym2.Init
public import Mathlib.Tactic.NormNum.GCD

public section

namespace CFSG.LocalAnalysis

namespace CyclicPair

open Subgroup MulAction

variable {G Ω : Type*} [Group G] [MulAction G Ω]

@[expose] def pointStab (A : Subgroup G) (α : Ω) : Subgroup (normalizer (A : Set G)) :=
  (stabilizer G α).subgroupOf (normalizer (A : Set G))

@[expose] def pairCore (A : Subgroup G) (α : Ω) : Subgroup (normalizer (A : Set G)) :=
  (pointStab A α).normalCore

instance (A : Subgroup G) (α : Ω) : (pairCore A α).Normal :=
  Subgroup.normalCore_normal _

variable [Finite G]

end CyclicPair

end CFSG.LocalAnalysis
