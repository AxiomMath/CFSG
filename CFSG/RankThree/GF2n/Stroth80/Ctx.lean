module

public import CFSG.RankThree.GF2n.Stroth80.Defs

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement

variable {G : Type} [Group G]

structure Ctx (M Q Z B : Subgroup G) : Prop where
  hyp : StrothHyp M Q Z
  conj : ∃ g : G, B = conjSubgroup g Z
  le : B ≤ Q
  ne : B ≠ Z

@[expose] def Width (Q Z : Subgroup G) (n : ℕ) : Prop := Nat.card Q = Nat.card Z ^ (2 * n + 1)

@[expose] def CQt (Q Z S : Subgroup G) : Set G := {x | x ∈ Q ∧ ∀ t ∈ S, ⁅t, x⁆ ∈ Z}

@[expose] def Vt (M L B Z : Subgroup G) (t : G) : Subgroup G :=
  Z ⊔ ⨆ (m : G) (_ : m ∈ M) (_ : t ∈ conjSubgroup m L), conjSubgroup m B

@[expose] def CNt (M L B Z : Subgroup G) (t : G) : Set G :=
  {r | r ∈ Rt M L t ∧ ∀ v ∈ Vt M L B Z t, ⁅r, v⁆ ∈ Z}

end CFSG.RankThree.GF2n.Stroth80
