module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.GH74.GLS.Basic
public import CFSG.RankThree.PartTwo.Sec4.Statements
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.RankThree.PartTwo.Sec14.Ronan148B

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.LocalRank CFSG.GH74.GLS

@[expose] def KF148D4Comm : Prop :=
  ∀ (Γ : Type) [Group Γ] [Finite Γ] (S : Subgroup Γ) (n : ℕ), 1 ≤ n →
    CFSG.Blueprint.ChevalleyExceptionalModel ↥S .trialityD4 2 n →
    ∀ ε : Γ, ε ^ 3 = 1 → Sec4.InducesOuterTheta ε S →
    (∃ K₀ : Subgroup Γ, K₀ ≤ S ⊓ Subgroup.centralizer ({ε} : Set Γ) ∧ Group.IsPerfect K₀ ∧
      (K₀.subgroupOf (S ⊓ Subgroup.centralizer ({ε} : Set Γ))).IsSubnormal ∧
      Sec4.IsoLThreePi ↥K₀ 2 n) →
    ∀ b a : Γ, b ∈ S ⊓ Subgroup.centralizer ({ε} : Set Γ) →
      a ∈ S ⊓ Subgroup.centralizer ({ε} : Set Γ) → a * b = b * a → orderOf b = 3 → a ^ 3 = 1 →
    ∀ V : Subgroup Γ,
      V ≤ pPrimeCoreOf 3 (S ⊓ Subgroup.centralizer ({ε} : Set Γ) ⊓
        Subgroup.centralizer ({b} : Set Γ)) →
      a ∈ Subgroup.normalizer (V : Set Γ) → V = ⁅V, Subgroup.zpowers a⁆ → V ≠ ⊥ →
      b ∈ ⁅V, S ⊓ Subgroup.centralizer ({b} : Set Γ)⁆

end CFSG.RankThree.PartTwo.Sec14.Ronan148B
