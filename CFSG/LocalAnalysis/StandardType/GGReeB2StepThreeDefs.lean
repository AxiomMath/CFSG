module

public import CFSG.LocalAnalysis.StandardType.GGReeB2CondCDefs

public section

namespace CFSG.StandardType.ReeB2Fixed

@[expose] def resolve (e : ℕ) (A B : Finset (Fin e)) : Finset (Fin e) :=
  symmDiff A B ∪ ((A ∩ B).filter fun p => succσ e p ∉ B).image (succσ e)

@[expose] def SyncAt (e : ℕ) (A B : Finset (Fin e)) (p : Fin e) : Prop :=
  p ∉ A ∧ p ∉ B ∧ (succσ e p ∈ A ↔ succσ e p ∈ B)

@[expose] def pstar (e : ℕ) (A B : Finset (Fin e)) (p : Fin e) (α β : Bool) : Bool :=
  let u := xor β (decide (succσ e p ∈ B))
  if p ∈ B then !u else α && !u

end CFSG.StandardType.ReeB2Fixed
