module

public import CFSG.Quasithin.EmptyFaithful.R3c23Def

public section

namespace CFSG.Quasithin.C116Three

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.R3c23 CFSG.Assembly.LowTwoRank

section Defs

variable {V : Type} [CommGroup V]

@[expose] def Bounds (G : Subgroup (MulAut V)) (W C : Subgroup V) : Prop :=
  ∀ B : Subgroup (MulAut V), B ≤ G → IsElemAbelian2 B →
    Nat.card B * Nat.card ↥(fixV B ⊓ W) ≤ Nat.card W ∧
    Nat.card B ^ 2 * Nat.card ↥(fixV B ⊓ W) * Nat.card ↥(fixMod B W C) ≤ Nat.card W ^ 2

@[expose] def TightFixes (P : Subgroup (MulAut V)) (M : Subgroup V) (w : V) : Prop :=
  ∀ B : Subgroup (MulAut V), B ≤ P → IsElemAbelian2 B →
    Nat.card B * Nat.card ↥(fixV B ⊓ M) = Nat.card M → ∀ b ∈ B, b w = w

@[expose] def CoreFixed (G : Subgroup (MulAut V)) (M : Subgroup V) : Prop :=
  ∀ P : Subgroup (MulAut V), P ≤ G → IsPGroup 2 P → ∃ w ∈ M, w ∉ fixV G ∧ ∀ x ∈ P, x w = w

end Defs

end CFSG.Quasithin.C116Three
