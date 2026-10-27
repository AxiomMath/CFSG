module

public import CFSG.Quasithin.Recognition.St84.AppTreeSAE
public import CFSG.Quasithin.Recognition.St84.Gen.G2qAmalDefs

public section

namespace CFSG.Quasithin.F112R.St84

open CFSG.Open
open scoped commutatorElement

variable {H : Type} [Group H] [Finite H]

structure G2qEdgeData (L1 L2 S : Subgroup H) (f : ℕ) : Prop where
  local_ : G2qLocalData (oTwoPrime (f112saP1' L1 L2 S)) (oTwoPrime (f112saP2' L1 L2 S))
    (S ⊓ f112saK L1 L2 S) f
  indec_left : ⁅pCoreOf 2 (f112saP1' L1 L2 S), oTwoPrime (f112saP1' L1 L2 S)⁆ =
    pCoreOf 2 (f112saP1' L1 L2 S)
  indec_right : ⁅pCoreOf 2 (f112saP2' L1 L2 S), oTwoPrime (f112saP2' L1 L2 S)⁆ =
    pCoreOf 2 (f112saP2' L1 L2 S)
  relCent_left : ∀ x ∈ pCoreOf 2 (f112saP2' L1 L2 S),
    (∀ l ∈ oTwoPrime (f112saP2' L1 L2 S),
      ⁅x, l⁆ ∈ centerOf (pCoreOf 2 (f112saP2' L1 L2 S))) →
    x ∈ pCoreOf 2 (f112saP1' L1 L2 S)
  gen_left : ∀ N : Subgroup H, centerOf (pCoreOf 2 (f112saP2' L1 L2 S)) ≤ N →
    N ≤ pCoreOf 2 (f112saP1' L1 L2 S) →
    oTwoPrime (f112saP1' L1 L2 S) ≤ Subgroup.normalizer (N : Set H) →
    N = pCoreOf 2 (f112saP1' L1 L2 S)
  torus_left : ∃ J : Subgroup H,
    J ≤ bigB (oTwoPrime (f112saP1' L1 L2 S)) (oTwoPrime (f112saP2' L1 L2 S))
      (S ⊓ f112saK L1 L2 S) ∧
    Odd (Nat.card J) ∧
    (∀ j ∈ J, ∀ l ∈ oTwoPrime (f112saP1' L1 L2 S), ⁅j, l⁆ ∈ pCoreOf 2 (f112saP1' L1 L2 S)) ∧
    pCoreOf 2 (f112saP1' L1 L2 S) ⊓ Subgroup.centralizer (J : Set H) = ⊥

end CFSG.Quasithin.F112R.St84

end
