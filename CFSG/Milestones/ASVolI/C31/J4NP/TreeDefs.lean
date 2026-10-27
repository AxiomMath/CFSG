module

public import CFSG.Milestones.ASVolI.C31.J4NP.HClDefs
public import Certificates.Data.CFSGNative.J4Tree.Index

public section

namespace CFSG.ASVolI

open CFSG.Sporadic.J4 CFSG.Sporadic.J4.QT CFSG.J4Tree.Native

@[expose] noncomputable def burnsideJ4NP_treeElt (ce : ℕ × ℕ) : J := eta uJ 11 ce.1 * Kel ce.2

@[expose] noncomputable def burnsideJ4NP_Rep (k : ℕ) : Subgroup J :=
  Subgroup.closure {g | g ∈ (treeBasis k).map burnsideJ4NP_treeElt}

@[expose] noncomputable def burnsideJ4NP_Wv (k : ℕ) : Subgroup J :=
  Subgroup.closure {g | g ∈ (treeWv k).map burnsideJ4NP_treeElt}

@[expose] def burnsideJ4NP_TreeStep (k : ℕ) : Prop :=
  ∀ x ∈ Hj ⊓ Subgroup.centralizer (burnsideJ4NP_Rep k : Set J), burnsideJ4NP_Is2A x →
    x ∉ burnsideJ4NP_Rep k → ∀ B : Subgroup J,
      burnsideJ4NP_IsHCl (burnsideJ4NP_Rep k ⊔ Subgroup.zpowers x) B →
      Nat.card ↥B ≤ 2 ^ 10 → Nat.card ↥(B ⊓ Eg uJ 11) ≤ 2 ^ 6 →
      ∃ k', 1 ≤ k' ∧ k' ≤ treeN ∧ ∃ h ∈ Hj,
        B = (burnsideJ4NP_Rep k').map (MulAut.conj h).toMonoidHom

@[expose] def burnsideJ4NP_TopFacts : Prop :=
  (∀ k ∈ treeTopIds, burnsideJ4NP_TreeStep k) ∧
    ∀ k ∈ treeTopKids,
      Nat.card ↥(Hj ⊓ Subgroup.centralizer (burnsideJ4NP_Rep k : Set J)) = treeOrd k

end CFSG.ASVolI
