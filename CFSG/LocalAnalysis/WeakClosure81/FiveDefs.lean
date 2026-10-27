module

public import CFSG.Quasithin.Background.B6Defs
public import CFSG.Assembly.LowTwoRankDefs

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open Subgroup

variable {G : Type} [Group G] [Finite G]

structure Sec5Hyp (H M A : Subgroup G) : Prop where
  isElemAbelian : IsElemAbelian 2 A
  le_group : A ≤ H
  le_M : A ≤ M
  not_le : ¬ H ≤ M
  odd_relIndex : Odd (M.relIndex H)

@[expose] def dFam (H M A : Subgroup G) : Set (Subgroup G) :=
  {D | D ≤ H ∧ A ≤ D ∧ ¬ D ≤ M ∧ Odd (M.relIndex D) ∧ (maxOver D A).ncard = 1}

theorem mem_dFam {H M A D : Subgroup G} :
    D ∈ dFam H M A ↔ D ≤ H ∧ A ≤ D ∧ ¬ D ≤ M ∧ Odd (M.relIndex D) ∧ (maxOver D A).ncard = 1 :=
  Iff.rfl

@[expose] def IsMinNormalOver (H Y X : Subgroup G) : Prop :=
  Y < X ∧ X ≤ H ∧ (X.subgroupOf H).Normal ∧
    ∀ Z : Subgroup G, Y ≤ Z → Z ≤ X → (Z.subgroupOf H).Normal → Z = Y ∨ Z = X

abbrev KerQuot (M H : Subgroup G) : Type := ↥H ⧸ (M.subgroupOf H).normalCore

def kerQuotMk (M H : Subgroup G) : ↥H →* KerQuot M H :=
  QuotientGroup.mk' (M.subgroupOf H).normalCore

def kerQuotImg (M H X : Subgroup G) : Subgroup (KerQuot M H) :=
  (X.subgroupOf H).map (kerQuotMk M H)

end CFSG.LocalAnalysis.WeakClosure81
