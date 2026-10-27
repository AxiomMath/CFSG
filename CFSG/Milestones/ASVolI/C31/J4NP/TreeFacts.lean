module

public import CFSG.Milestones.ASVolI.C31.J4NP.TreeBFS
public import CFSG.Milestones.ASVolI.C31.J4NP.Is2AAffNative
public import Certificates.Data.CFSGNative.J4Tree.Tree

public section

namespace CFSG.ASVolI

open CFSG.Sporadic.J4 CFSG.Sporadic.J4.QT CFSG.J4Tree.Native CFSG.J4Tree.Native.Node
open CFSG.Quasithin.J4Loc (omegaZ)

@[expose] def burnsideJ4NP_treeTest : Code → Bool :=
  burnsideJ4NP_affine2AWith (burnsideJ4NP_sextArr ())

@[expose] def burnsideJ4NP_MergeFact (k k' : ℕ) (y : J) : Prop :=
  ∃ h ∈ Hj, burnsideJ4NP_Rep k ⊔ Subgroup.zpowers y ≤
      (burnsideJ4NP_Rep k').map (MulAut.conj h).toMonoidHom ∧
    Nat.card ↥(Hj ⊓ Subgroup.centralizer
      ((burnsideJ4NP_Rep k ⊔ Subgroup.zpowers y : Subgroup J) : Set J)) ≤ treeOrd k'

@[expose] def burnsideJ4NP_PrunedFact (k : ℕ) (y : J) : Prop :=
  2 ^ 10 < Nat.card ↥(omegaZ (Hj ⊓ Subgroup.centralizer
      ((burnsideJ4NP_Rep k ⊔ Subgroup.zpowers y : Subgroup J) : Set J))) ∨
    2 ^ 6 < Nat.card ↥(omegaZ (Hj ⊓ Subgroup.centralizer
      ((burnsideJ4NP_Rep k ⊔ Subgroup.zpowers y : Subgroup J) : Set J)) ⊓ Eg uJ 11)

@[expose] def burnsideJ4NP_NodeFacts (k : ℕ) : Prop :=
  treeOrd k = 2 ^ Nat.log2 (treeOrd k) ∧
    treeOrd k ≤ Nat.card ↥(Hj ⊓ Subgroup.centralizer (burnsideJ4NP_Rep k : Set J)) ∧
    (Nat.card ↥(Hj ⊓ Subgroup.centralizer (burnsideJ4NP_Rep k : Set J)) = treeOrd k →
      omegaZ (Hj ⊓ Subgroup.centralizer (burnsideJ4NP_Rep k : Set J)) = burnsideJ4NP_Rep k ∧
      ∃ ys : List J,
        (∀ y ∈ ys, burnsideJ4NP_PrunedFact k y ∨
          ∃ k', 1 ≤ k' ∧ k' ≤ treeN ∧ k' ∉ treeTopIds ∧ burnsideJ4NP_MergeFact k k' y) ∧
        ∀ x ∈ Hj ⊓ Subgroup.centralizer (burnsideJ4NP_Rep k : Set J), x * x = 1 →
          x ∉ burnsideJ4NP_Rep k → burnsideJ4NP_treeTest (burnsideJ4NP_encJ x) = true →
          ∃ y ∈ ys, ∃ n ∈ Hj, burnsideJ4NP_Rep k ⊔ Subgroup.zpowers x =
            (burnsideJ4NP_Rep k ⊔ Subgroup.zpowers y).map (MulAut.conj n).toMonoidHom)

@[expose] def burnsideJ4NP_EdgeFact (k₀ k : ℕ) : Prop :=
  ∃ y : J, Nat.card ↥(Hj ⊓ Subgroup.centralizer (burnsideJ4NP_Rep k₀ : Set J)) = treeOrd k₀ →
    burnsideJ4NP_MergeFact k₀ k y

@[expose] def burnsideJ4NP_TreeChunkFacts (c : ℕ) : Prop :=
  (∀ k, 100 * c ≤ k → k < 100 * c + 100 → 1 ≤ k → k ≤ treeN → k ∉ treeTopIds →
      burnsideJ4NP_NodeFacts k) ∧
    (∀ k, 1 ≤ k → k ≤ treeN → (treeParent k).1 / 100 = c → 1 ≤ (treeParent k).1 →
      burnsideJ4NP_EdgeFact (treeParent k).1 k) ∧
    (c = 0 → globalOK = true)

@[expose] def burnsideJ4NP_WFacts : Prop :=
  ∀ k, 1 ≤ k → k ≤ treeN → burnsideJ4NP_Rep k ≤ Hj ∧
    Subgroup.closure {x | x ∈ burnsideJ4NP_Rep k ∧ x * x = 1 ∧ x ≠ 1 ∧
      burnsideJ4NP_treeTest (burnsideJ4NP_encJ x) = true} = burnsideJ4NP_Wv k

end CFSG.ASVolI
