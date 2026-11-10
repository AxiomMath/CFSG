
module

public import CFSG.Sporadic.FischerOddCore.Fi22ExtCheckBase
public import CFSG.Monster.B.Fischer.Fi22GraphBase
public import CFSG.Sporadic.FischerOddCore.Fi22ExtCheckInputs
public meta import CFSG.Sporadic.FischerOddCore.Fi22ExtData
public meta import CFSG.Monster.B.Fischer.Fi22OuterCheckBase
public meta import Certificates.Data.CFSGNative.MonsterB.Co2Chain
public import CFSG.Monster.B.Fischer.Fi22GraphCheckBase
public import CFSG.Monster.B.Fischer.PinnedChain
public import Mathlib

@[expose] public noncomputable section

namespace CFSG.Sporadic.FischerOddCore

open CFSG.Certificates CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Monster.B.Fischer

def fi22ExtPerm (L : ℕ) : Equiv.Perm (Fin 3510) := permOfArr 3510 (fi22ExtArr L)

def fi22ExtPerm256 (L : ℕ) : Equiv.Perm (Fin 256) := permOfArr 256 (fi22ExtArr256 L)

def fi22ExtQ : Equiv.Perm (Fin 3510) := fi22ExtPerm 0

def fi22ExtV : Equiv.Perm (Fin 3510) := fi22ExtPerm 1

def fi22ExtSubGen (k : ℕ) : Equiv.Perm (Fin 3510) := fi22ExtPerm (2 + k)

def fi22ExtFullGen (k : ℕ) : Equiv.Perm (Fin 3510) := fi22ExtPerm (11 + k)

def fi22ExtRep (k : ℕ) : Equiv.Perm (Fin 3510) := fi22ExtPerm (21 + k)

def fi22ExtSylowRep (j : ℕ) : Equiv.Perm (Fin 3510) := fi22ExtPerm (27 + j)

def fi22ExtConj (j : ℕ) : Equiv.Perm (Fin 3510) := fi22ExtPerm (106 + j)

def fi22ExtClassSize (j : ℕ) : ℕ := fi22ExtClassSizes.getD j 0

def fi22ExtGlobalClass (j : ℕ) : ℕ := fi22ExtGlobalClasses.getD j 0

def fi22ExtT0 : Subgroup (Equiv.Perm (Fin 3510)) :=
  fi22OuterT.map (MulAut.conj fi22ExtQ).toMonoidHom

def fi22ExtS : Subgroup (Equiv.Perm (Fin 3510)) :=
  Subgroup.closure (insert fi22ExtV (fi22ExtT0 : Set (Equiv.Perm (Fin 3510))))

def fi22ExtDeltaPt (i : Fin 256) : Fin 3510 :=
  ⟨fi22ExtSmallPointsNat.getD i 0 % 3510, Nat.mod_lt _ (by norm_num)⟩

def fi22ExtDelta : List (Fin 3510) := List.ofFn fi22ExtDeltaPt

def fi22ExtSmallChain : RawSchreierDatum 256 :=
  RawSchreierDatum.ofArrays 256 (by decide) fi22ExtSmallStrong fi22ExtSmallGenCount
    (by rw [fi22ExtSmallStrong, Array.size_ofFn]; decide)
    (fi22FinList 256 (by decide) fi22ExtSmallBase) (by decide)
    (fi22WordsArr fi22ExtSmallGenCount 18 fi22ExtSmallDerivations)

end CFSG.Sporadic.FischerOddCore
