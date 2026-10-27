
module

public import CFSG.Monster.B.Fischer.PinnedChainBase
public import CFSG.Monster.B.Fischer.Fi22CertData
public import CFSG.Monster.B.Fischer.Fi22FormsData
public import CFSG.Monster.B.Fischer.Fi22Monomials
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.ZMod.Basic
public meta import CFSG.Monster.B.Fischer.PinnedChainBase
public meta import CFSG.Monster.B.Fischer.Fi22CertData
public meta import CFSG.Monster.B.Fischer.Fi22FormsData
public meta import Certificates.Data.CFSGNative.Fi22Pinned.Forms
public import CFSG.Monster.B.Fischer.Fi22CertInputs
public import CFSG.Monster.B.Fischer.PinnedChainInputs

@[expose] public section

namespace CFSG.Monster.B.Fischer

open CFSG.Monster.B.Fischer.Native CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native

@[expose] def fi22SchemaVersion : Nat := 1

@[expose] def fi22GroupName : String := "Fi22"

@[expose] def fi22Prime : Nat := 3

@[expose] def fi22Dimension : Nat := 77

abbrev Fi22V : Type := Fin 77 → ZMod 3

@[expose] noncomputable def fi22Quad (c : Nat → Nat) (v : Fi22V) : ZMod 3 :=
  ∑ i : Fin 77, ∑ j : Fin 77, if i ≤ j then (c (pairIdx i j) : ZMod 3) * v i * v j else 0

@[expose] def fi22FormCoeff (r k : Nat) : Nat := trit fi22FormsBytes (752 * r) k

@[expose] noncomputable def fi22Form (r : Nat) : Fi22V → ZMod 3 := fi22Quad (fi22FormCoeff r)

@[expose] def fi22X : Set (Fi22V → ZMod 3) := {q | ∃ r < 3510, fi22Form r = q}

@[expose] def fi22InvCoeff (k : Nat) : Nat := trit fi22InvFormBytes 0 k

@[expose] noncomputable def fi22InvForm : Fi22V → ZMod 3 := fi22Quad fi22InvCoeff

@[expose] noncomputable def polarMatrix (q : Fi22V → ZMod 3) : Matrix (Fin 77) (Fin 77) (ZMod 3) :=
  fun i j => q (Pi.single i 1 + Pi.single j 1) - q (Pi.single i 1) - q (Pi.single j 1)

@[expose] noncomputable def fi22B : Matrix (Fin 77) (Fin 77) (ZMod 3) := polarMatrix fi22InvForm

@[expose] def fi22CentralizerIdx : List Nat := [0, 1, 2, 3, 4, 10]

@[expose] def fi22CentralizerRank : Nat := 5928

@[expose] noncomputable def fi22C0 : Equiv.Perm (Fin 3510) := fi22GenPerm 0

@[expose] noncomputable def fi22C1 : Equiv.Perm (Fin 3510) := fi22GenPerm 0 * fi22GenPerm 1

@[expose] def fi22Point : Fin 3510 := 0

@[expose] noncomputable def fi22H0 : Subgroup (Equiv.Perm (Fin 3510)) :=
  Subgroup.closure {g | ∃ j ∈ fi22StabIdx, fi22StrongPerm j = g}

end CFSG.Monster.B.Fischer
