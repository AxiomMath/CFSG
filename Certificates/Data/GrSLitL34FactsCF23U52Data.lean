module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsCF23U52Points
public import CFSG.Sporadic.SmallOddCore.CentData
public import Certificates.Data.CFSGNative.Schreier.Check
public import Mathlib

public section

namespace CFSG.ComponentClassification.GSThmB.U52

open CFSG.Sporadic.Th.Native CFSG.Sporadic.SmallOddCore CFSG.Sporadic.SmallOddCore.Native
  CFSG.Certificates.Native CFSG.Monster.B.Co2.Native

@[expose] def codeA : ℕ := 1104008183840

@[expose] def codeB : ℕ := 1838666383372

@[expose] def matA : Matrix (Fin 5) (Fin 5) CFSG.Fischer.F4 := matN codeA

@[expose] def matB : Matrix (Fin 5) (Fin 5) CFSG.Fischer.F4 := matN codeB

@[expose] def tabA : Array ℕ := tabN codeA

@[expose] def tabB : Array ℕ := tabN codeB

@[expose] def chainS : Array (Array ℕ) := #[
    tabA, tabB, tabN 1021137073651713, tabN 70979213086723, tabN 844631096999939,
    tabN 844609806901251, tabN 281479288520705, tabN 281483583619073, tabN 844631138902019]

@[expose] def chainW : Array (List ℤ) := #[
    [], [], [-1, 2], [2, 1, 1], [-4, -3, -3, 4, 4, -3], [4, 5, -4], [6, 6, 6], [5, -6, 5, -6],
    [-7, -8, -5, -8, 7, -5]]

@[expose] def chainBase : List (Fin 341) := [0, 1, 16, 4, 64]

@[expose] def baseArr : Array ℕ := (chainBase.map Fin.val).toArray

@[expose] def u52Levels : Array Level := rawLevels 341 chainS baseArr

@[expose] def tbl (a : Array ℕ) : Table := a.map UInt32.ofNat

@[expose] def tblN (k : ℕ) : Table := tbl (tabN k)

@[expose] def pgTbls : Array Table := #[tbl tabA, tbl tabB]

@[expose] def pgInvTbls : Array Table := pgTbls.map (invT 341)

@[expose] def u52Sift (T : Table) : Bool := siftA 341 u52Levels baseArr 0 (natArr T)

@[expose] def uTbl : Table := tbl frobTab

@[expose] def sylowGenTbls : List Table :=
  [tblN 338775203954025, tblN 89353621990077,
    tblN 804734416917121, uTbl]

@[expose] def u52SylowOrder : ℕ := 2048

@[expose] def u52Rows : List ClassRow := [
  { rep := tblN 281543700398081, outer := false, classSize := 165,
    centOrder := 82944, centGens := [
      tblN 821267861355133, tblN 3891555262528, tblN 141605365649411],
    oddPrimes := [3], odd := [
      { rep := tblN 489650862857813, prime := 3, classSize := 768,
        wit := .conj (tblN 23270528497468) 12 },
      { rep := tblN 347536842694658, prime := 3, classSize := 192,
        wit := .conj (tblN 70391835411772) 6 },
      { rep := tblN 844652823687171, prime := 3, classSize := 64,
        wit := .conj (tblN 918804977501118) 6 },
      { rep := tblN 2473917944000, prime := 3, classSize := 384,
        wit := .conj (tblN 517251329269739) 12 },
      { rep := tblN 400082207364585, prime := 3, classSize := 768,
        wit := .conj (tblN 680436214392489) 6 },
      { rep := tblN 325589240721411, prime := 3, classSize := 192,
        wit := .conj (tblN 140803811580692) 6 },
      { rep := tblN 563130455416834, prime := 3, classSize := 64,
        wit := .conj (tblN 424823462999618) 6 },
      { rep := tblN 866552924893186, prime := 3, classSize := 48,
        wit := .conj (tblN 518624938914667) 6 },
      { rep := tblN 656843681916246, prime := 3, classSize := 48,
        wit := .conj (tblN 560684497782633) 6 }] },
  { rep := tblN 70643626295297, outer := false, classSize := 2970,
    centOrder := 4608, centGens := [
      tblN 385231390378346, tblN 385231249141823],
    oddPrimes := [3], odd := [
      { rep := tblN 678856063151466, prime := 3, classSize := 16,
        wit := .conj (tblN 637033162044777) 6 },
      { rep := tblN 1010132268823171, prime := 3, classSize := 32,
        wit := .conj (tblN 365433443689794) 6 },
      { rep := tblN 517688475490665, prime := 3, classSize := 128,
        wit := .conj (tblN 1010132268823171) 6 },
      { rep := tblN 960399776120171, prime := 3, classSize := 16,
        wit := .conj (tblN 347579834400770) 6 },
      { rep := tblN 822343798956994, prime := 3, classSize := 32,
        wit := .conj (tblN 738518641168406) 6 }] },
  { rep := uTbl, outer := true, classSize := 19008,
    centOrder := 720, centGens := [
      tblN 353017337746756, tblN 300189512433925],
    oddPrimes := [3, 5], odd := [
      { rep := tblN 70373056184321, prime := 3, classSize := 40,
        wit := .conj (tblN 92360340226372) 2 },
      { rep := tblN 356316192194821, prime := 3, classSize := 40,
        wit := .conj (tblN 287317545784336) 2 },
      { rep := tblN 75883819110661, prime := 5, classSize := 144,
        wit := .conj (tblN 281497613440081) 4 }] }]

end CFSG.ComponentClassification.GSThmB.U52
