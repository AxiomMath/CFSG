module

public import CFSG.Sporadic.SmallOddCore.CentSpec
public import CFSG.Sporadic.Schreier.PairMcLCert
public meta import Certificates.Data.CFSGNative.SmallOddCore.Check
public meta import CFSG.Sporadic.SmallOddCore.CentData

public section

namespace CFSG.Sporadic.SmallOddCore

open Subgroup CFSG.Sporadic.Th.Native CFSG.Sporadic.SmallOddCore.Native CFSG.Sporadic.Schreier

@[expose] def mclCentHex : String := include_str "McLCent.txt"

@[expose] def mclCentTbl (k : ℕ) : Table := hexT 3 275 (275 * k) mclCentHex

@[expose] def mclOuterTbl : Table := mclCentTbl 0

@[expose] def mclSylowGenTbls : List Table := (List.range 3).map fun i => mclCentTbl (i + 1)

@[expose] def mclRows : List ClassRow := [
  { rep := mclCentTbl 4, outer := false, classSize := 22275,
    centOrder := 40320, centGens := [mclCentTbl 5, mclCentTbl 6],
    oddPrimes := [3, 5, 7], odd := [
      { rep := mclCentTbl 7, prime := 3, classSize := 112, wit := .conj (mclCentTbl 8) 4 },
      { rep := mclCentTbl 9, prime := 7, classSize := 2880, wit := .conj (mclCentTbl 10) 6 },
      { rep := mclCentTbl 11, prime := 7, classSize := 2880, wit := .conj (mclCentTbl 12) 14 },
      { rep := mclCentTbl 13, prime := 5, classSize := 1344, wit := .conj (mclCentTbl 14) 14 },
      { rep := mclCentTbl 15, prime := 3, classSize := 1120, wit := .conj (mclCentTbl 16) 10 }]
  },
  { rep := mclCentTbl 17, outer := true, classSize := 113400,
    centOrder := 7920, centGens := [mclCentTbl 18, mclCentTbl 19, mclCentTbl 20, mclCentTbl 21],
    oddPrimes := [3, 5, 11], odd := [
      { rep := mclCentTbl 22, prime := 5, classSize := 1584, wit := .conj (mclCentTbl 23) 4 },
      { rep := mclCentTbl 24, prime := 11, classSize := 720, wit := .conj (mclCentTbl 25) 8 },
      { rep := mclCentTbl 26, prime := 11, classSize := 720, wit := .conj (mclCentTbl 27) 8 },
      { rep := mclCentTbl 28, prime := 3, classSize := 440, wit := .conj (mclCentTbl 29) 2 }]
  }]

@[expose] def mclSylowOrder : ℕ := 256

@[expose] noncomputable def mclU : Equiv.Perm (Fin 275) := tp 275 mclOuterTbl

@[expose] noncomputable def mclR : Subgroup (Equiv.Perm (Fin 275)) := mclP ⊔ zpowers mclU

@[expose] noncomputable def mclS : Subgroup (Equiv.Perm (Fin 275)) :=
  closure (tp 275 '' {x | x ∈ mclSylowGenTbls.toArray})

@[expose] noncomputable def mclC (r : ClassRow) : Subgroup (Equiv.Perm (Fin 275)) :=
  closure (tp 275 '' {x | x ∈ r.centGens.toArray})

end CFSG.Sporadic.SmallOddCore
