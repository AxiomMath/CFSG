module

public import CFSG.Quasithin.Recognition.St84.AppTreeSAE
public import CFSG.Quasithin.Recognition.St84.Gen.L2SectionBorel

public section

namespace CFSG.Quasithin.F112R.St84

open CFSG.Open
open scoped MatrixGroups commutatorElement

variable {H : Type} [Group H] [Finite H]

structure TransferLeftData (L1 L2 S : Subgroup H) : Prop where
  nat_right : ∃ (F : Type) (_ : Field F) (_ : CharP F 2)
    (α : ↥(oTwoPrime (f112saP2' L1 L2 S)) →* SL(2, F)), Function.Surjective α ∧
      α.ker = CFSG.pCore 2 ↥(oTwoPrime (f112saP2' L1 L2 S)) ∧
      IsNatSecOf (oTwoPrime (f112saP2' L1 L2 S))
        (centerOf (pCoreOf 2 (oTwoPrime (f112saP2' L1 L2 S)))) ⊥ α
  centerRight_le : centerOf (pCoreOf 2 (f112saP2' L1 L2 S)) ≤ pCoreOf 2 (f112saP1' L1 L2 S)
  commutator_le : ⁅pCoreOf 2 (f112saP1' L1 L2 S), pCoreOf 2 (f112saP1' L1 L2 S)⁆ ≤
    centerOf (pCoreOf 2 (f112saP1' L1 L2 S))
  centerLeft_le : centerOf (pCoreOf 2 (f112saP1' L1 L2 S)) ≤
    Subgroup.centralizer (oTwoPrime (f112saP1' L1 L2 S) : Set H)
  gen_left : ∀ N : Subgroup H, centerOf (pCoreOf 2 (f112saP1' L1 L2 S)) ≤ N →
    centerOf (pCoreOf 2 (f112saP2' L1 L2 S)) ≤ N → N ≤ pCoreOf 2 (f112saP1' L1 L2 S) →
    oTwoPrime (f112saP1' L1 L2 S) ≤ Subgroup.normalizer (N : Set H) →
    N = pCoreOf 2 (f112saP1' L1 L2 S)
  torus_left : ∃ J : Subgroup H,
    J ≤ bigB (oTwoPrime (f112saP1' L1 L2 S)) (oTwoPrime (f112saP2' L1 L2 S))
      (S ⊓ f112saK L1 L2 S) ∧
    Odd (Nat.card J) ∧
    (∀ j ∈ J, ∀ l ∈ oTwoPrime (f112saP1' L1 L2 S), ⁅j, l⁆ ∈ pCoreOf 2 (f112saP1' L1 L2 S)) ∧
    pCoreOf 2 (f112saP1' L1 L2 S) ⊓ Subgroup.centralizer (J : Set H) = ⊥
  indec_left : ⁅pCoreOf 2 (f112saP1' L1 L2 S), oTwoPrime (f112saP1' L1 L2 S)⁆ =
    pCoreOf 2 (f112saP1' L1 L2 S)
  eq_one_of_mem_trivOTwoQuot : ∀ k ∈ oTwoPrime (f112saP2' L1 L2 S), Odd (orderOf k) →
    k ∈ trivOTwoQuot (oTwoPrime (f112saP1' L1 L2 S)) → k = 1

end CFSG.Quasithin.F112R.St84

end
