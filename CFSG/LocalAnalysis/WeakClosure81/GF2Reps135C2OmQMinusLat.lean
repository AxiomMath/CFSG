module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2OmQPlusSigned
public import Mathlib.Data.ZMod.Basic

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.StandardType

abbrev OmqMinusLat (l m h : ℕ) : Type := (Fin l → ZMod m) × ZMod h

@[expose] def omqMinusAct {l m h : ℕ} (π : Equiv.Perm (Fin l)) (s : Fin l → ℤ)
    (ν : OmqMinusLat l m h) : OmqMinusLat l m h :=
  (omqSignedAct π s ν.1, ((∏ a, s a : ℤ) : ZMod h) * ν.2)

@[expose] def OmqMinusInOrbit {l m h : ℕ} (ν u : OmqMinusLat l m h) : Prop :=
  ∃ (π : Equiv.Perm (Fin l)) (s : Fin l → ℤ), SpIsSign s ∧ omqMinusAct π s ν = u

@[expose] def OmqMinusShape {l : ℕ} (hl : 2 ≤ l) (π : Equiv.Perm (Fin l)) (s : Fin l → ℤ) :
    Prop :=
  ((∀ a, s a = 1) ∧ π * π = 1 ∧ π ⟨0, by omega⟩ = ⟨1, by omega⟩ ∧
      π ⟨1, by omega⟩ = ⟨0, by omega⟩) ∨
    (π = 1 ∧ s ⟨0, by omega⟩ = -1 ∧ Odd (Finset.univ.filter fun a => s a = -1).card)

@[expose] def omqSignedActZ {l : ℕ} (π : Equiv.Perm (Fin l)) (s : Fin l → ℤ) (v : Fin l → ℤ) :
    Fin l → ℤ :=
  fun b => s (π.symm b) * v (π.symm b)

@[expose] def OmqFormalInOrbit {l : ℕ} (v u : Fin l → ℤ) : Prop :=
  ∃ (π : Equiv.Perm (Fin l)) (s : Fin l → ℤ), SpIsSign s ∧ omqSignedActZ π s v = u

@[expose] def omqMinusSimple (l : ℕ) (t : Fin l) : Equiv.Perm (Fin l) × (Fin l → ℤ) :=
  if h : t.val + 1 < l then (Equiv.swap t ⟨t.val + 1, h⟩, 1) else (1, spSgn t)

@[expose] def omqMinusFlag (l j : ℕ) : Fin l → ℤ := fun b => if b.val ≤ j then 1 else 0

@[expose] def omqMinusCube (l : ℕ) : Fin l → ℤ := fun _ => 1

@[expose] def omqMinusTriv (l m h j : ℕ) (hl : 1 ≤ l) : OmqMinusLat l m h :=
  (Pi.single ⟨0, by omega⟩ (-(j : ZMod m)), -(j : ZMod h))

end CFSG.LocalAnalysis.WeakClosure81
