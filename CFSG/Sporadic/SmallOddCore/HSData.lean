module

public import CFSG.Sporadic.SmallOddCore.CentSpec
public import CFSG.Sporadic.Schreier.PairHSCert
public meta import Certificates.Data.CFSGNative.SmallOddCore.Check
public meta import CFSG.Sporadic.SmallOddCore.CentData

public section

namespace CFSG.Sporadic.SmallOddCore

open Subgroup CFSG.Sporadic.Th.Native CFSG.Sporadic.SmallOddCore.Native CFSG.Sporadic.Schreier

@[expose] def hsCentHex : String := include_str "HSCent.txt"

@[expose] def hsCentTbl (k : ℕ) : Table := hexT 3 3850 (3850 * k) hsCentHex

@[expose] def hsOuterTbl : Table := hsCentTbl 0

@[expose] def hsSylowGenTbls : List Table := (List.range 4).map fun i => hsCentTbl (i + 1)

@[expose] def hsRows : List ClassRow := [
  { rep := hsCentTbl 5, outer := false, classSize := 5775,
    centOrder := 7680, centGens := [hsCentTbl 6, hsCentTbl 7],
    oddPrimes := [3, 5], odd := [
      { rep := hsCentTbl 8, prime := 5, classSize := 384, wit := .conj (hsCentTbl 9) 6 },
      { rep := hsCentTbl 10, prime := 3, classSize := 320, wit := .conj (hsCentTbl 11) 12 }]
  },
  { rep := hsCentTbl 12, outer := false, classSize := 15400,
    centOrder := 2880, centGens := [hsCentTbl 13, hsCentTbl 14, hsCentTbl 15, hsCentTbl 16],
    oddPrimes := [3, 5], odd := [
      { rep := hsCentTbl 17, prime := 5, classSize := 144, wit := .conj (hsCentTbl 18) 2 },
      { rep := hsCentTbl 19, prime := 3, classSize := 80, wit := .conj (hsCentTbl 20) 4 }]
  },
  { rep := hsCentTbl 21, outer := true, classSize := 1100,
    centOrder := 40320, centGens := [hsCentTbl 22, hsCentTbl 23, hsCentTbl 24, hsCentTbl 25],
    oddPrimes := [3, 5, 7], odd := [
      { rep := hsCentTbl 26, prime := 5, classSize := 1344, wit := .conj (hsCentTbl 27) 4 },
      { rep := hsCentTbl 28, prime := 7, classSize := 5760, wit := .conj (hsCentTbl 29) 6 },
      { rep := hsCentTbl 30, prime := 3, classSize := 1120, wit := .conj (hsCentTbl 31) 6 },
      { rep := hsCentTbl 32, prime := 3, classSize := 112, wit := .conj (hsCentTbl 33) 2 }]
  },
  { rep := hsCentTbl 34, outer := true, classSize := 23100,
    centOrder := 1920, centGens := [hsCentTbl 35, hsCentTbl 36, hsCentTbl 37, hsCentTbl 38],
    oddPrimes := [3, 5], odd := [
      { rep := hsCentTbl 39, prime := 5, classSize := 384, wit := .conj (hsCentTbl 40) 6 },
      { rep := hsCentTbl 41, prime := 3, classSize := 80, wit := .conj (hsCentTbl 42) 2 }]
  }]

@[expose] def hsSylowOrder : ℕ := 1024

@[expose] noncomputable def hsU : Equiv.Perm (Fin 3850) := tp 3850 hsOuterTbl

@[expose] noncomputable def hsR : Subgroup (Equiv.Perm (Fin 3850)) := hsP ⊔ zpowers hsU

@[expose] noncomputable def hsS : Subgroup (Equiv.Perm (Fin 3850)) :=
  closure (tp 3850 '' {x | x ∈ hsSylowGenTbls.toArray})

@[expose] noncomputable def hsC (r : ClassRow) : Subgroup (Equiv.Perm (Fin 3850)) :=
  closure (tp 3850 '' {x | x ∈ r.centGens.toArray})

end CFSG.Sporadic.SmallOddCore
