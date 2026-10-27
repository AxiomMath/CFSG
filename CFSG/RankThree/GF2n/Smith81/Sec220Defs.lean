module

public import CFSG.RankThree.GF2n.Stroth80.Defs

public section

namespace CFSG.RankThree.GF2n.Smith81

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
  CFSG.RankThree.GF2n CFSG.RankThree.GF2n.Stroth80
open scoped commutatorElement

variable {G : Type} [Group G]

@[expose] def Cv (v : G) : Subgroup G := Subgroup.centralizer ({v} : Set G)

@[expose] def Nv (v : G) : Subgroup G := Subgroup.normalizer (Subgroup.zpowers v : Set G)

@[expose] def Mv (M : Subgroup G) (v : G) : Subgroup G := M ⊓ Cv v

@[expose] def Qv (Q : Subgroup G) (v : G) : Subgroup G := Q ⊓ Cv v

theorem mem_Cv {v g : G} : g ∈ Cv v ↔ g * v = v * g := Subgroup.mem_centralizer_singleton_iff

@[expose] def IsDihOddZ (Z : Subgroup G) (z v : G) : Prop :=
  (∃ x y : G, IsConj z x ∧ IsConj z y ∧ Commute x z ∧ Commute y z ∧ v = x * y) ∧
    Odd (orderOf v) ∧ 1 < orderOf v

@[expose] def ZConjBy (H Z : Subgroup G) : Set (Subgroup G) :=
  {A | ∃ y ∈ H, A = conjSubgroup y Z}

@[expose] def LinkV (v : G) (A B : Subgroup G) : Prop := B ≤ QB A ⊓ Cv v

@[expose] def BlockRel (H Z : Subgroup G) (v : G) (A B : Subgroup G) : Prop :=
  A ∈ ZConjBy H Z ∧ B ∈ ZConjBy H Z ∧ LinkV v A B

@[expose] def BlockOf (H Z : Subgroup G) (v : G) : Set (Subgroup G) :=
  {A | Relation.EqvGen (BlockRel H Z v) Z A}

@[expose] def BlockStab (H Z : Subgroup G) (v : G) : Subgroup G where
  carrier := {g | g ∈ H ∧ ∀ A, A ∈ BlockOf H Z v ↔ conjSubgroup g A ∈ BlockOf H Z v}
  mul_mem' := fun {a b} ha hb => ⟨H.mul_mem ha.1 hb.1, fun A => by
    rw [conjSubgroup_mul]; exact (hb.2 A).trans (ha.2 _)⟩
  one_mem' := ⟨H.one_mem, fun A => by rw [conjSubgroup_one]⟩
  inv_mem' := fun {g} hg => ⟨H.inv_mem hg.1, fun A => by
    have := hg.2 (conjSubgroup g⁻¹ A)
    rw [← conjSubgroup_mul, mul_inv_cancel, conjSubgroup_one] at this
    exact this.symm⟩

@[expose] def N1 (Z : Subgroup G) (v : G) : Subgroup G := BlockStab (Nv v) Z v

@[expose] def EBlock (Z : Subgroup G) (v : G) : Subgroup G :=
  Subgroup.closure (⋃ A ∈ BlockOf (Nv v) Z v, (A : Set G))

@[expose] def DHat (Z : Subgroup G) (v : G) : Subgroup G :=
  Subgroup.centralizer (EBlock Z v : Set G) ⊓ N1 Z v

theorem le_EBlock_of_mem {Z : Subgroup G} {v : G} {A : Subgroup G}
    (hA : A ∈ BlockOf (Nv v) Z v) :
    A ≤ EBlock Z v := fun x hx =>
  Subgroup.subset_closure (Set.mem_iUnion₂.mpr ⟨A, hA, hx⟩)

section Normality

variable {Z : Subgroup G}

theorem conj_EBlock_le_of_mem_N1 {v g : G} (hg : g ∈ N1 Z v) :
    conjSubgroup g (EBlock Z v) ≤ EBlock Z v := by
  refine Subgroup.map_le_iff_le_comap.mpr ((Subgroup.closure_le _).mpr
    (Set.iUnion₂_subset fun A hA x hx => ?_))
  have hAg : conjSubgroup g A ∈ BlockOf (Nv v) Z v := (hg.2 A).mp hA
  have hmem : g * x * g⁻¹ ∈ conjSubgroup g A := by
    rw [mem_conjSubgroup]; simpa [mul_assoc] using hx
  exact le_EBlock_of_mem hAg hmem

theorem N1_le_normalizer_EBlock {v : G} : N1 Z v ≤ Subgroup.normalizer (EBlock Z v : Set G) := by
  intro g hg
  refine conjSubgroup_eq_self_iff.mp (le_antisymm (conj_EBlock_le_of_mem_N1 hg) fun x hx => ?_)
  rw [mem_conjSubgroup]
  have h1 := conj_EBlock_le_of_mem_N1 (inv_mem hg)
  have : g⁻¹ * x * g ∈ conjSubgroup g⁻¹ (EBlock Z v) := by
    rw [mem_conjSubgroup]; simpa [mul_assoc] using hx
  exact h1 this

theorem dHat_normal {v : G} : ((DHat Z v).subgroupOf (N1 Z v)).Normal :=
  Subgroup.normal_subgroupOf_of_le_normalizer fun g hg =>
    Subgroup.inf_normalizer_le_normalizer_inf
      ⟨mem_normalizer_centralizer (N1_le_normalizer_EBlock hg), Subgroup.le_normalizer hg⟩

end Normality

section Blocks

variable [Finite G] {M Q Z : Subgroup G}

theorem ZConjBy.self (H : Subgroup G) : Z ∈ ZConjBy H Z :=
  ⟨1, H.one_mem, (conjSubgroup_one Z).symm⟩

end Blocks

instance dHatNormal (Z : Subgroup G) (v : G) : ((DHat Z v).subgroupOf (N1 Z v)).Normal :=
  dHat_normal

end CFSG.RankThree.GF2n.Smith81

