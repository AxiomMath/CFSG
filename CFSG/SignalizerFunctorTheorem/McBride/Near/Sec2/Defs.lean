module

public import CFSG.SignalizerFunctorTheorem.McBride.Near.Defs

public section

open CFSG.Open

namespace CFSG.SignalizerFunctorTheorem.McBride.Near

variable {Γ : Type*} [Group Γ]

structure NearAction (p : ℕ) (A G : Subgroup Γ) : Prop where
  prime : p.Prime
  odd : p ≠ 2
  elemAbelian : IsElemAbelian p A
  admits : Admits A G
  nearPSolvable : signalizerNearPSolvable p ↥G

structure NearAsolvAction (p : ℕ) (A G : Subgroup Γ) : Prop extends NearAction p A G where
  solvable_cen : Group.IsSolvable ↥(cenIn G A)

structure SemisimpleAction (p : ℕ) (A G : Subgroup Γ) : Prop extends NearAsolvAction p A G where
  semisimple : IsSemisimple G
  ne_bot : G ≠ ⊥

@[expose] def layerIn (G : Subgroup Γ) : Subgroup Γ :=
  (CFSG.layer ↥G).map G.subtype

@[expose] def mOf (A G : Subgroup Γ) : Subgroup Γ :=
  norIn G (cenIn G (CFSG.fittingSubgroupOf (cenIn G A)))

@[expose] def kJ (A J : Subgroup Γ) : Subgroup Γ :=
  norIn J (cenIn J (CFSG.fittingSubgroupOf (cenIn J (norIn A J))))

@[expose] def scalSet (X A D : Subgroup Γ) : Set (Subgroup Γ) :=
  {S | S ≤ X ∧ Admits ((X ⊓ D) ⊔ A) S ∧ Group.IsSolvable S}

@[expose] def scalJoin (X A D : Subgroup Γ) : Subgroup Γ :=
  ⨆ S ∈ scalSet X A D, S

@[expose] def k1 (G W : Subgroup Γ) : Subgroup Γ :=
  cenIn (kOf G) W

@[expose] def k2 (G W : Subgroup Γ) : Subgroup Γ :=
  cenIn (kOf G) (k1 G W)

@[expose] def s0 (G S : Subgroup Γ) : Subgroup Γ :=
  S ⊓ kOf G

@[expose] def d0 (A G S : Subgroup Γ) : Subgroup Γ :=
  cenIn G A ⊓ s0 G S

@[expose] def d1 (A G S : Subgroup Γ) : Subgroup Γ :=
  CFSG.fittingSubgroupOf (d0 A G S)

@[expose] def s1 (G S : Subgroup Γ) : Subgroup Γ :=
  CFSG.fittingSubgroupOf (s0 G S)

@[expose] def d2 (A G S : Subgroup Γ) : Subgroup Γ :=
  d0 A G S ⊓ sectionCentralizer (d1 A G S) (d0 A G S)

@[expose] def s2 (G S : Subgroup Γ) : Subgroup Γ :=
  s0 G S ⊓ sectionCentralizer (s1 G S) (s0 G S)

end CFSG.SignalizerFunctorTheorem.McBride.Near
