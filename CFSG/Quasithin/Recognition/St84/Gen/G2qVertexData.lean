module

public import CFSG.Quasithin.Recognition.St84.Gen.G2qAmalDefs

public section

namespace CFSG.Quasithin.F112R.St84

open CFSG.Open
open scoped commutatorElement

variable {G : Type*} [Group G]

structure G2qVertexData (L1 L2 S : Subgroup G) (f : ℕ) : Prop extends G2qLocalData L1 L2 S f where
  indec_left : ⁅pCoreOf 2 L1, L1⁆ = pCoreOf 2 L1
  gen_left : ∀ N : Subgroup G, centerOf (pCoreOf 2 L2) ≤ N → N ≤ pCoreOf 2 L1 →
    L1 ≤ Subgroup.normalizer (N : Set G) → N = pCoreOf 2 L1

end CFSG.Quasithin.F112R.St84

end
