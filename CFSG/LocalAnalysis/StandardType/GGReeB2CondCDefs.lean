module

public import Mathlib.Data.ZMod.Basic

public section

namespace CFSG.StandardType.ReeB2Fixed

@[expose] def S (e : ℕ) (J : Finset (Fin e)) : ZMod (2 ^ e - 1) := ∑ j ∈ J, 2 ^ (j : ℕ)

@[expose] def digits (e : ℕ) (x : ZMod (2 ^ e - 1)) : Finset (Fin e) :=
  Finset.univ.filter fun j => x.val.testBit j

@[expose] def R (e : ℕ) : ZMod (2 ^ e - 1) := 2 ^ ((e + 1) / 2) - 1

@[expose] def units (e : ℕ) : Finset (ZMod (2 ^ e - 1)) := {1, -1, R e, -R e}

@[expose] def Lam (e : ℕ) (J : Finset (Fin e)) : Set (ZMod (2 ^ e - 1)) :=
  {x | ∃ c : Fin e → ZMod (2 ^ e - 1), (∀ j ∈ J, c j ∈ units e) ∧ x = ∑ j ∈ J, c j * 2 ^ (j : ℕ)}

@[expose] def Good (e : ℕ) (J : Finset (Fin e)) : Prop := (0 : ZMod (2 ^ e - 1)) ∉ Lam e J

@[expose] def Admissible (e : ℕ) (A B : Finset (Fin e)) : Prop :=
  Good e A ∧ Good e B ∧ Disjoint (Lam e A) (Lam e B)

@[expose] def CondC (e : ℕ) : Prop :=
  ∀ A B : Finset (Fin e), Admissible e A B →
    ∃ κ ∈ Lam e A, ¬ Admissible e (digits e (S e B - κ)) (digits e (S e B + κ))

@[expose] def Delta (e : ℕ) (J : Finset (Fin e)) : Set (ZMod (2 ^ e - 1)) :=
  {x | ∃ d : Fin e → ZMod (2 ^ e - 1),
    (∀ j ∈ J, d j ∈ ({0, -1, 2 ^ ((e - 1) / 2) - 1, -2 ^ ((e - 1) / 2)} : Finset _)) ∧
      x = ∑ j ∈ J, d j * 2 ^ (j : ℕ)}

@[expose] def succσ (e : ℕ) (p : Fin e) : Fin e :=
  ⟨(p + (e + 1) / 2) % e, Nat.mod_lt _ (Nat.pos_of_ne_zero (by rintro rfl; exact p.elim0))⟩

@[expose] def IndepSigma (e : ℕ) (A : Finset (Fin e)) : Prop := ∀ p ∈ A, succσ e p ∉ A

@[expose] def term (e : ℕ) (t : Bool) (p : Fin e) : ZMod (2 ^ e - 1) :=
  if t then 2 ^ (p : ℕ) * R e else 2 ^ (p : ℕ)

@[expose] def Slots (e : ℕ) (A : Finset (Fin e)) (t : Fin e → Bool) (U : Finset (Fin e)) : Prop :=
  ∀ p ∈ A, if t p then succσ e p ∈ U else (p ∈ U ∨ succσ e p ∈ U)

@[expose] def IM (e : ℕ) : Prop :=
  ∀ A B : Finset (Fin e), IndepSigma e A → Admissible e A B →
    ∃ t : Fin e → Bool, Slots e A t (digits e (S e B + ∑ p ∈ A, term e (t p) p))

end CFSG.StandardType.ReeB2Fixed
