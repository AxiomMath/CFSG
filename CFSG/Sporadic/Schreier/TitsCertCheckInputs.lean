module

public import CFSG.Sporadic.Schreier.TitsArrays
public import CFSG.Sporadic.Schreier.TitsBasic
public meta import CFSG.Sporadic.Schreier.TitsData
public meta import CFSG.Sporadic.Schreier.TitsArrays
public meta import CFSG.Sporadic.Schreier.TitsBasic
public meta import Certificates.Data.CFSGNative.Schreier.Check
public meta import Certificates.Data.CFSGNative.MonsterB.Co2Chain
public meta import Certificates.Data.CFSGNative.MonsterB.Co2Data
public meta import CFSG.Certificates.NativeSchreierCard
public import CFSG.Certificates.NativeSchreierCard
public meta import Mathlib.GroupTheory.Schreier
public import Mathlib.GroupTheory.Schreier

public section

namespace CFSG.Sporadic.Schreier.Tits

open CFSG.Certificates.Native CFSG.Monster.B.Co2.Native

@[expose] def titsU (j : ℕ) : List ℤ := (titsDerivedComm.getD j ([], [])).1

@[expose] def titsV (j : ℕ) : List ℤ := (titsDerivedComm.getD j ([], [])).2

@[expose] def titsPerfR (j : ℕ) : List ℤ := (titsPerfectComm.getD j ([], [])).1

@[expose] def titsPerfS (j : ℕ) : List ℤ := (titsPerfectComm.getD j ([], [])).2

@[expose] def titsDArr (j : ℕ) : Array ℕ :=
  commArr 1755 (wordArr 1755 titsGenArrs (titsU j)) (wordArr 1755 titsGenArrs (titsV j))

@[expose] def titsDArrs : Array (Array ℕ) := Array.ofFn (n := 2) fun j => titsDArr j.val

@[expose] def titsEArr (j : ℕ) : Array ℕ :=
  commArr 1755 (wordArr 1755 titsDArrs (titsPerfR j)) (wordArr 1755 titsDArrs (titsPerfS j))

end CFSG.Sporadic.Schreier.Tits
