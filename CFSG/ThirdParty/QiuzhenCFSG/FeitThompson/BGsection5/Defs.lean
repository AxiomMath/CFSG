module
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection3.Defs

public import CFSG.ThirdParty.QiuzhenCFSG.Theory.Representation.CyclicQuotientExtension
public import CFSG.ThirdParty.QiuzhenCFSG.Theory.Representation.SolvableDimension
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.LinearAlgebra.PrimitiveRootEigenspaces
public import CFSG.ThirdParty.QiuzhenCFSG.Theory.Representation.ExtraspecialFixedPoints
public import CFSG.ThirdParty.QiuzhenCFSG.Theory.Representation.TwoDimensionalOddOrder
public import Mathlib.Algebra.CharP.LinearMaps
public import Mathlib.LinearAlgebra.Eigenspace.Triangularizable
public import Mathlib.LinearAlgebra.Eigenspace.Zero
public import Mathlib.LinearAlgebra.Lagrange
public import Mathlib.LinearAlgebra.Semisimple
public import Mathlib.LinearAlgebra.TensorProduct.Pi
public import Mathlib.RepresentationTheory.Character
public import Mathlib.RepresentationTheory.Coinduced
public import Mathlib.RepresentationTheory.Semisimple
public import Mathlib.RepresentationTheory.Submodule
public import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
public import Mathlib.RingTheory.SimpleModule.Isotypic
public import Mathlib.RingTheory.ZMod.Torsion
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection1.CriticalSubgroupLemmas
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.Burnside.NormalComplement
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.Extraspecial
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.LinearAlgebra.BlockElementaryMap
public import CFSG.ThirdParty.QiuzhenCFSG.Theory.Representation.ConjugateRep
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection2.EndFieldRep
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.GeneratorRank
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection4.Defs
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PCore.PCore
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PGroup.NormalSubgroups
import Mathlib.GroupTheory.Schreier

namespace CFSG
end CFSG
open CFSG

/-! # Definitions for BG Section 5 -/

section

/-- Elementary abelian `p`-subgroups of order `p^n`. -/
@[expose] public def CFSG.elementaryAbelianSubgroupsOfRank (p n : ℕ) (G : Type*) [Group G] :
    Set (Subgroup G) :=
  {A | Nat.card A = p ^ n ∧ IsElementaryAbelian p A}

/-- Maximal elementary abelian `p`-subgroups. -/
@[expose] public def CFSG.maximalElementaryAbelianSubgroups (p : ℕ) (G : Type*) [Group G] :
    Set (Subgroup G) :=
  {A | IsElementaryAbelian p A ∧
    ∀ B : Subgroup G, A ≤ B → IsElementaryAbelian p B → A = B}

/- The group rank, defined through elementary abelian subgroups. -/
-- @[expose] public noncomputable def groupRank (G : Type*) [Group G] : ℕ :=
--   sSup {n : ℕ | ∃ p : ℕ, Nat.Prime p ∧
--     ∃ A : Subgroup G, A ∈ elementaryAbelianSubgroupsOfRank p n G}

/-- Blackburn's `SCN_n(G)`: self-centralizing normal subgroups of rank at least `n`. -/
@[expose] public noncomputable def CFSG.scnSubgroups (n : ℕ) (G : Type*) [Group G] :
    Set (Subgroup G) :=
  {A | A.Normal ∧ Subgroup.centralizer (A : Set G) = A ∧ n ≤ groupRank A}

/-- The subgroup `Ω₁(Z(G))` inside `G`. -/
@[expose] public def Ω₁Z (p : ℕ) (G : Type*) [Group G] : Subgroup G :=
  (omega₁ (G := Subgroup.center G) (p := p)).map (Subgroup.center G).subtype

/-- The subgroup `Ω₁(Z₂(G))` inside `G`. -/
public abbrev Ω₁Z₂ (p : ℕ) (G : Type*) [Group G] : Subgroup G :=
  z2OmegaCandidate p

public abbrev CFSG.CΩ₁Z₂ (p : ℕ) (G : Type*) [Group G] : Subgroup G :=
  Subgroup.centralizer (Ω₁Z₂ p G : Set G)

/-- A finite `p`-group is narrow if it has rank at most two, or if it admits a subgroup of
order `p` whose centralizer splits with a cyclic complement. -/
@[expose] public noncomputable def CFSG.IsNarrowPGroup
    (p : ℕ) (G : Type*) [Group G] [Finite G] : Prop :=
  IsPGroup p G ∧ (groupRank G ≤ 2 ∨ (∃ R₀ R₁ : Subgroup G, Nat.card R₀ = p ∧ IsCyclic R₁ ∧
      Disjoint R₀ R₁ ∧ Subgroup.centralizer (R₀ : Set G) = R₀ ⊔ R₁))

end

public theorem CFSG.generatorRank_le_natCard_local
    (G : Type*) [Group G] [Finite G] :
    generatorRank G ≤ Nat.card G := by
  letI : Fintype G := Fintype.ofFinite G
  obtain ⟨S, hS_card, _hS_top⟩ := Group.rank_spec G
  calc
    generatorRank G = Group.rank G := generatorRank_eq_group_rank G
    _ = S.card := by rw [← hS_card]
    _ ≤ Fintype.card G := by simpa using Finset.card_le_univ S
    _ = Nat.card G := by simp [Nat.card_eq_fintype_card]

public theorem CFSG.generatorRank_le_groupRank_of_commutative_pgroup
    {p : ℕ} [Fact p.Prime]
    (G : Type*) [Group G] [Finite G] [IsMulCommutative G] [Fact (IsPGroup p G)] :
    generatorRank G ≤ groupRank G := by
  have hprimeRank_le_natCard : ∀ q : ℕ, primeRank q G ≤ Nat.card G := by
    intro q
    rw [primeRank]
    refine csSup_le ?_ ?_
    · exact ⟨0, ⊥, IsPGroup.of_bot (p := q) (G := G), inferInstance, Nat.zero_le _⟩
    · intro n hn
      rcases hn with ⟨A, _hAp, _hAcomm, hnA⟩
      exact hnA.trans <| (generatorRank_le_natCard_local A).trans (Subgroup.card_le_card_group A)
  have htop_rank : generatorRank (⊤ : Subgroup G) = generatorRank G := by
    rw [generatorRank_eq_group_rank, generatorRank_eq_group_rank]
    exact Group.rank_congr Subgroup.topEquiv
  have hprimeRank : generatorRank G ≤ primeRank p G := by
    rw [primeRank]
    refine le_csSup ?_ ?_
    · exact ⟨Nat.card G, fun n hn => by
        rcases hn with ⟨A, _hAp, _hAcomm, hnA⟩
        exact hnA.trans <| (generatorRank_le_natCard_local A).trans (Subgroup.card_le_card_group A)⟩
    · exact ⟨⊤, by simpa using (Fact.out : IsPGroup p G).to_subgroup (⊤ : Subgroup G),
        inferInstance, by simp [htop_rank]⟩
  rw [groupRank]
  refine le_csSup ?_ ?_
  · exact ⟨Nat.card G, fun n hn => by
      rcases hn with ⟨q, _hq, hnq⟩
      exact hnq.trans (hprimeRank_le_natCard q)⟩
  · exact ⟨p, Fact.out, hprimeRank⟩
