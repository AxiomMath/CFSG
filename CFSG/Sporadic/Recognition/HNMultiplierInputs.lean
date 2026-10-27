module

public import Certificates.Data.CFSGNative.Bridge.HNGPL
public import CFSG.Sporadic.Recognition.CoverRecipeSq

public section

namespace CFSG.Sporadic.Recognition.HNMultiplier

open CFSG.CosetTable CFSG.LieType.Multipliers CFSG.Sporadic.Recognition.CoverRecipe
open CFSG.Sporadic.Th.Native CFSG.Sporadic.F5.Native CFSG.Sporadic.Fi23.Native
open CFSG.Sporadic.Bridge.SurjD.Native

@[expose] def ofCodes (c : List ℕ) : List (Fin 7 × Bool) :=
  c.map (fun x => (⟨x / 2 % 7, Nat.mod_lt _ (by norm_num)⟩, decide (x % 2 = 0)))

abbrev hnTL : List (Fin 7) := subsetOf 7 [0, 1, 2, 3, 4, 5]

abbrev hnS1L : List (Fin hnTL.length) := subsetOf hnTL.length [0, 1, 2, 3, 4]

abbrev hnS2L : List (Fin hnS1L.length) := subsetOf hnS1L.length [0, 1]

@[expose] def hnEmbed (w : List (Fin hnS1L.length × Bool)) : List (Fin 7 × Bool) :=
  w.map fun l => (hnTL.get (hnS1L.get l.1), l.2)

theorem hnS1L_length : hnS1L.length = 5 := by decide

@[expose] def hnRelCodesBC : List (List ℕ) :=
  [[8, 8, 8, 8],
   [9, 9, 1, 8, 8, 0],
   [0, 0, 0, 0, 0, 0, 0],
   [8, 0, 0, 8, 0, 0, 8, 0, 0, 8, 0, 0],
   [9, 9, 8, 0, 8, 0, 0, 0, 8, 0, 8, 0, 0, 0, 8, 0, 8, 0, 0, 0],
   [8, 0, 8, 0, 8, 0, 8, 1, 1, 1, 8, 0, 8, 0, 8, 0, 8, 1, 1, 1],
   [4, 4, 8, 8],
   [9, 5, 8, 4],
   [1, 9, 1, 5, 0, 8, 0, 4],
   [0, 8, 0, 0, 0, 4, 0, 8, 0, 0, 0, 4, 0, 8, 0, 0, 0, 4],
   [10, 10],
   [8, 10, 8, 10],
   [1, 11, 0, 10],
   [0, 5, 1, 5, 10, 4, 0, 4, 1, 4, 10, 4, 10, 4, 10],
   [12, 12, 12, 12, 12],
   [9, 12, 8, 12, 12],
   [5, 12, 4, 13, 13],
   [13, 1, 12, 0],
   [10, 12, 10, 12, 10, 12]]

@[expose] def hnEDefCodes : List ℕ := [7, 10, 4, 10]

@[expose] def hnGDefCodes : List ℕ := [3, 4, 0, 5]

@[expose] def hnRelCodes1 : List (List ℕ) :=
  [[8, 8, 8, 8],
   [7, 7, 9, 9],
   [6, 9, 6, 9],
   [5, 8, 5, 8],
   [4, 4, 9, 9],
   [8, 0, 8, 8, 1, 8],
   [7, 5, 6, 4, 6, 4],
   [0, 0, 0, 0, 0, 0, 0],
   [0, 8, 0, 4, 1, 9, 1, 5],
   [0, 9, 0, 6, 1, 9, 1, 6],
   [0, 5, 1, 7, 0, 5, 1, 6],
   [0, 6, 1, 6, 5, 0, 5, 1, 6, 5, 6],
   [1, 5, 1, 5, 1, 1, 9, 1, 4, 1, 4, 1, 1, 8],
   [9, 4, 1, 1, 5, 1, 5, 0, 0, 8, 0, 9, 1, 1, 5, 1, 1, 9, 0, 0],
   [0, 6, 1, 1, 6, 0, 0, 6, 1, 8, 0, 0, 8, 1, 8, 0, 9, 1, 8, 0, 8, 6, 0],
   [8, 1, 8, 1, 1, 1, 9, 5, 1, 1, 1, 9, 1, 9, 5, 0, 5, 8, 1, 1, 9, 5, 0, 5],
   [0, 8, 0, 0, 0, 4, 8, 1, 1, 1, 9, 4, 0, 0, 6, 0, 5, 8, 0, 8, 0, 9, 0, 9, 6],
   [8, 0, 6, 0, 8, 1, 6, 1, 8, 6, 1, 9, 0, 9, 1, 6, 1, 8, 0, 6, 0, 8, 6, 0, 9, 1],
   [1, 5, 8, 6, 1, 5, 8, 1, 7, 1, 1, 5, 1, 1, 8, 1, 4, 7, 8, 1, 8, 5, 1, 7, 1, 1, 5, 1, 1, 8],
   [0, 4, 0, 0, 7, 0, 9, 0, 9, 0, 4, 9, 0, 5, 7, 8, 1, 9, 1, 4, 9, 1, 9, 5, 1, 7, 1, 1, 4, 1, 4, 9],
   [8, 0, 8, 1, 8, 0, 8, 1, 9, 4, 1, 9, 1, 9, 6, 1, 9, 5, 1, 7, 1, 1, 5, 1, 1, 1, 4, 1, 4, 1,
    4, 1, 1, 1],
   [9, 1, 7, 0, 0, 7, 1, 1, 6, 0, 0, 7, 0, 9, 1, 1, 5, 1, 1, 8, 0, 5, 7, 1, 9, 4, 1, 8, 6, 1,
    9, 1, 1, 1, 5],
   [0, 8, 1, 8, 6, 1, 7, 1, 9, 0, 7, 0, 7, 5, 0, 4, 0, 0, 6, 0, 5, 9, 0, 8, 0, 8, 1, 1, 1, 4,
    0, 0, 6, 0, 6, 4, 0, 0, 5],
   [1, 4, 1, 4, 0, 6, 0, 8, 0, 8, 0, 4, 9, 0, 6, 8, 1, 1, 4, 0, 4, 0, 0, 8, 0, 0, 7, 0, 8, 0,
    8, 0, 4, 9, 0, 6, 9, 1, 1, 1, 8, 1],
   [5, 1, 1, 4, 6, 1, 7, 1, 1, 5, 1, 1, 1, 4, 0, 7, 0, 8, 1, 7, 1, 9, 7, 1, 8, 0, 8, 7, 4, 0,
    0, 0, 4, 0, 0, 6, 0, 6, 4, 0, 0, 4, 7, 8],
   [0, 0, 5, 0, 5, 0, 5, 1, 1, 4, 0, 0, 6, 0, 7, 5, 0, 5, 0, 9, 0, 0, 0, 6, 0, 8, 4, 0, 9, 5,
    1, 4, 1, 5, 1, 6, 8, 0, 8, 0, 9, 0, 9, 5, 0, 7],
   [7, 1, 1, 1, 9, 0, 7, 9, 0, 9, 5, 0, 8, 1, 1, 5, 7, 1, 7, 1, 1, 5, 0, 0, 4, 1, 4, 1, 4, 1,
    1, 8, 6, 1, 1, 5, 7, 1, 7, 1, 1, 5, 0, 0, 4, 1, 4, 1, 4, 1, 5, 1],
   [8, 1, 1, 1, 9, 0, 7, 9, 0, 9, 5, 0, 9, 4, 0, 0, 0, 4, 0, 0, 6, 0, 6, 4, 0, 5, 0, 9, 1, 1,
    1, 8, 0, 6, 9, 0, 9, 4, 0, 9, 5, 0, 0, 0, 4, 0, 0, 6, 0, 6, 4, 0, 4, 0],
   [0, 0, 4, 0, 0, 6, 0, 7, 5, 0, 5, 7, 9, 1, 1, 7, 1, 5, 7, 1, 7, 1, 1, 8, 0, 7, 0, 0, 9, 5,
    1, 1, 1, 9, 0, 0, 4, 0, 0, 6, 0, 6, 4, 0, 9, 5, 7, 1, 1, 7, 1, 5, 7, 1, 7, 1, 1, 9, 0, 6,
    0, 0, 9, 5, 1, 1, 1, 9],
   [7, 0, 0, 0, 6, 0, 7, 5, 0, 6, 0, 0, 8, 6, 4, 1, 5, 7, 1, 7, 1, 1, 5, 1, 1, 8, 0, 0, 0, 4,
    8, 1, 1, 1, 9, 1, 1, 6, 1, 8, 0, 6, 0, 9, 6, 0, 8, 1, 7, 5, 6, 0, 0, 5, 0, 5, 0, 5, 1, 1,
    4, 0, 0, 6, 0, 6, 4, 0, 0, 9],
   [8, 0, 0, 7, 8, 0, 6, 0, 7, 9, 0, 0, 9, 1, 1, 5, 7, 1, 7, 1, 1, 5, 1, 1, 1, 8, 5, 7, 0, 9,
    1, 1, 5, 1, 1, 1, 8, 1, 9, 5, 1, 7, 1, 1, 1, 8, 1, 9, 7, 1, 1, 7, 1, 4, 6, 1, 7, 0, 0, 0,
    8, 1, 6, 8, 1, 8, 5, 1, 7, 1, 1, 5, 1],
   [6, 0, 0, 0, 6, 0, 7, 5, 0, 6, 0, 0, 8, 6, 4, 1, 5, 7, 1, 7, 1, 1, 5, 1, 1, 4, 0, 0, 6, 0,
    4, 8, 0, 9, 4, 0, 9, 1, 5, 7, 1, 7, 1, 1, 5, 1, 1, 1, 9, 5, 6, 0, 0, 5, 0, 5, 0, 5, 1, 1,
    4, 0, 0, 6, 0, 6, 4, 0, 0, 4, 8, 6, 9, 5],
   [6, 1, 8, 0, 6, 0, 7, 9, 0, 9, 1, 4, 7, 4, 0, 0, 5, 0, 5, 0, 5, 1, 1, 4, 0, 0, 6, 0, 7, 5,
    0, 0, 8, 0, 0, 0, 4, 0, 0, 6, 0, 6, 4, 0, 5, 0, 9, 0, 0, 0, 6, 0, 9, 5, 0, 6, 9, 0, 9, 1,
    1, 1, 6, 0, 6, 4, 0, 6, 0, 0, 7, 8, 5, 1, 4, 6, 1, 7, 1, 1, 5, 1, 1, 4, 0, 0, 6, 0, 9, 5,
    0, 8, 4, 7, 0, 9],
   [6, 9, 4, 1, 1, 5, 7, 1, 7, 1, 1, 5, 0, 0, 4, 1, 4, 1, 4, 1, 1, 6, 4, 7, 0, 8, 1, 8, 6, 1,
    7, 1, 8, 0, 6, 0, 6, 4, 9, 1, 1, 5, 7, 1, 7, 1, 1, 5, 0, 0, 4, 1, 4, 1, 4, 1, 1, 5, 7, 4,
    0, 8, 1, 9, 7, 1, 7, 1, 9, 0, 7, 0, 6, 4, 9, 1, 1, 5, 7, 1, 7, 1, 1, 5, 0, 0, 4, 1, 4, 1,
    4, 1, 1, 5, 7, 4, 0, 8, 1, 9, 7, 1, 7, 1, 9, 0, 7, 0]]

@[expose] def hnRelCodes2 : List (List ℕ) :=
  [[2, 2, 2, 2, 2, 2, 2],
   [0, 0, 0, 0, 0, 0, 0],
   [3, 0, 3, 0, 3, 0, 3, 0, 3, 0],
   [3, 1, 3, 1, 3, 1, 3, 1, 3, 1],
   [1, 3, 0, 2, 1, 3, 3, 1, 2, 0, 3, 1],
   [1, 3, 0, 2, 1, 3, 1, 3, 0, 2, 1, 3],
   [0, 3, 0, 0, 3, 0, 0, 3, 0, 0, 3, 0],
   [2, 2, 1, 3, 3, 1, 2, 1, 3, 1, 3, 1, 2, 0, 2, 0],
   [1, 1, 1, 3, 1, 3, 3, 1, 1, 3, 3, 3, 1, 3, 1, 1, 3, 3],
   [3, 1, 2, 1, 1, 1, 3, 1, 3, 0, 2, 0, 0, 2, 0, 3, 3, 1, 2, 2, 0, 3, 1, 3]]

@[expose] def hnConjCodes : List ℕ :=
  [0, 6, 1, 1, 6, 1, 4, 8, 0, 6, 8, 4, 1, 4, 6, 12, 10, 13, 13]

@[expose] def hnRelsBC : List (List (Fin 7 × Bool)) := hnRelCodesBC.map ofCodes

@[expose] def hnEDef : List (Fin 7 × Bool) := ofCodes hnEDefCodes

@[expose] def hnGDef : List (Fin 7 × Bool) := ofCodes hnGDefCodes

@[expose] def hnRels0 : List (List (Fin 7 × Bool)) := hnRelsBC ++ [hnEDef, hnGDef]

@[expose] def hnRels1 : List (List (Fin 7 × Bool)) := hnRelCodes1.map ofCodes

@[expose] def hnRels2 : List (List (Fin 7 × Bool)) := hnRelCodes2.map ofCodes

@[expose] def hnConj : List (Fin 7 × Bool) := ofCodes hnConjCodes

@[expose] def hnRc : List (Fin 7 × Bool) :=
  hnConj ++ [(5, true)] ++ FreeGroup.invRev hnConj ++ [(4, false), (4, false)]

@[expose] def hnRels : List (List (Fin 7 × Bool)) := hnRels0 ++ hnRels1 ++ hnRels2 ++ [hnRc]

@[expose] def hnCommCodes : Fin 7 → List (List ℕ × List ℕ)
  | 0 => [([2], [2, 1]), ([0, 0, 3], [0, 2, 0, 2, 2])]
  | 1 => [([0], [0, 3]), ([2, 2, 1], [2, 0, 2, 0, 0])]
  | 2 => [([0], [6]), ([6], [2, 6, 1])]
  | 3 => [([1], [4]), ([3, 6, 2], [4])]
  | 4 => [([3], [4, 6]), ([2, 1, 2], [6, 2, 0])]
  | 5 => [([8, 8], [12, 10, 0, 0, 4, 12, 8, 1, 1, 8, 0, 4, 1, 1, 8, 6, 1, 1, 1, 6, 4])]
  | 6 => [([8], [12, 10, 9, 0, 8, 1, 1, 4, 6, 0, 6, 4, 0, 8, 1, 4])]

@[expose] def ofCodes5 (c : List ℕ) : List (Fin hnS1L.length × Bool) :=
  c.map (fun x => (⟨x / 2 % hnS1L.length, Nat.mod_lt _ (by decide)⟩, decide (x % 2 = 0)))

@[expose] def hnCommWord5 (j : Fin hnS1L.length) : List (Fin hnS1L.length × Bool) :=
  commWords ((hnCommCodes ⟨j.val, by have := j.2; have h5 := hnS1L_length; omega⟩).map
    fun p => (ofCodes5 p.1, ofCodes5 p.2))

@[expose] def hnCommWord (i : Fin 7) : List (Fin 7 × Bool) :=
  if h : i.val < 5 then hnEmbed (hnCommWord5 ⟨i.val, by have h5 := hnS1L_length; omega⟩)
  else commWords ((hnCommCodes i).map fun p => (ofCodes p.1, ofCodes p.2))

abbrev hnCover : List (List (Fin 7 × Bool)) := cover₂Words hnRels hnCommWord

@[expose] def hnPlain1 : List (List (Fin 7 × Bool)) :=
  (restrictWords hnS1L (restrictWords hnTL hnRels)).map hnEmbed

@[expose] def hnNCodes : List (List ℕ) :=
  [[10, 0, 11, 1],
   [10, 8, 11, 8],
   [10, 4, 11, 7],
   [10, 6, 11, 5],
   [10, 2, 11, 6, 1, 7],
   [10, 10]]

@[expose] def hnNwords : List (List (Fin 7 × Bool)) := hnNCodes.map ofCodes

abbrev hnCoverPlus : List (List (Fin 7 × Bool)) := hnCover ++ (hnPlain1 ++ hnNwords)

@[expose] def hnTopCodes : List (List ℕ) :=
  [[10, 10],
   [8, 8, 8, 8],
   [4, 4, 8, 8],
   [9, 5, 8, 4],
   [3, 4, 0, 5],
   [10, 0, 11, 1],
   [10, 8, 11, 8],
   [10, 4, 11, 7],
   [10, 6, 11, 5],
   [9, 9, 1, 8, 8, 0],
   [10, 2, 11, 6, 1, 7],
   [0, 0, 0, 0, 0, 0, 0],
   [1, 9, 1, 5, 0, 8, 0, 4],
   [0, 13, 1, 12, 0, 1, 1, 13, 0, 12],
   [4, 13, 1, 12, 0, 5, 1, 13, 0, 12],
   [10, 13, 1, 12, 0, 11, 1, 13, 0, 12],
   [12, 13, 1, 12, 0, 13, 1, 13, 0, 12],
   [8, 0, 0, 8, 0, 0, 8, 0, 0, 8, 0, 0],
   [0, 12, 12, 12, 12, 12, 1, 13, 13, 13, 13, 13],
   [4, 12, 12, 12, 12, 12, 5, 13, 13, 13, 13, 13],
   [10, 12, 12, 12, 12, 12, 11, 13, 13, 13, 13, 13],
   [12, 12, 12, 12, 12, 12, 13, 13, 13, 13, 13, 13],
   [0, 9, 12, 8, 12, 12, 1, 13, 13, 9, 13, 8],
   [4, 9, 12, 8, 12, 12, 5, 13, 13, 9, 13, 8],
   [10, 9, 12, 8, 12, 12, 11, 13, 13, 9, 13, 8],
   [12, 9, 12, 8, 12, 12, 13, 13, 13, 9, 13, 8],
   [0, 5, 12, 4, 13, 13, 1, 12, 12, 5, 13, 4],
   [4, 5, 12, 4, 13, 13, 5, 12, 12, 5, 13, 4],
   [10, 5, 12, 4, 13, 13, 11, 12, 12, 5, 13, 4],
   [12, 5, 12, 4, 13, 13, 13, 12, 12, 5, 13, 4],
   [5, 0, 6, 1, 7, 6, 2, 6, 1, 7, 0, 7, 3],
   [7, 1, 4, 0, 5, 3, 6, 2, 4, 3, 7, 2, 5],
   [0, 10, 12, 10, 12, 10, 12, 1, 13, 11, 13, 11, 13, 11],
   [4, 10, 12, 10, 12, 10, 12, 5, 13, 11, 13, 11, 13, 11],
   [10, 10, 12, 10, 12, 10, 12, 11, 13, 11, 13, 11, 13, 11],
   [12, 10, 12, 10, 12, 10, 12, 13, 13, 11, 13, 11, 13, 11],
   [0, 8, 0, 0, 0, 4, 0, 8, 0, 0, 0, 4, 0, 8, 0, 0, 0, 4],
   [9, 3, 4, 6, 2, 7, 5, 2, 1, 2, 6, 2, 0, 3, 0, 3, 1, 3, 7],
   [9, 9, 8, 0, 8, 0, 0, 0, 8, 0, 8, 0, 0, 0, 8, 0, 8, 0, 0, 0],
   [8, 0, 8, 0, 8, 0, 8, 1, 1, 1, 8, 0, 8, 0, 8, 0, 8, 1, 1, 1],
   [1, 2, 2, 1, 3, 0, 3, 0, 0, 3, 0, 2, 0, 2, 2, 2, 1, 1, 3, 3, 1, 3, 1],
   [3, 0, 0, 3, 1, 2, 1, 2, 2, 1, 2, 0, 2, 0, 0, 0, 3, 3, 1, 1, 3, 1, 3],
   [13, 8, 12, 10, 9, 0, 8, 1, 1, 4, 6, 0, 6, 4, 0, 8, 1, 4, 9, 5, 0, 9, 1, 5, 7, 1, 7, 5, 0,
    0, 9, 1, 8, 11, 13],
   [11, 8, 8, 12, 10, 0, 0, 4, 12, 8, 1, 1, 8, 0, 4, 1, 1, 8, 6, 1, 1, 1, 6, 4, 9, 9, 5, 7, 0,
    0, 0, 7, 9, 0, 0, 5, 1, 9, 0, 0, 9, 13, 5, 1, 1, 11, 13]]

@[expose] def hnTop : List (List (Fin 7 × Bool)) := hnTopCodes.map ofCodes

abbrev hnL3 : List (List (Fin hnTL.length × Bool)) := restrictWords hnTL hnNwords

abbrev hnRelsMid : List (List (Fin 7 × Bool)) := hnRels1 ++ [hnGDef]

abbrev hnL2 : List (List (Fin hnS1L.length × Bool)) :=
  restrictWords hnS1L (restrictWords hnTL (cover₂Words hnRelsMid hnCommWord))

abbrev hnL1 : List (List (Fin hnS2L.length × Bool)) :=
  restrictWords hnS2L (restrictWords hnS1L (restrictWords hnTL (cover₂Words hnRels2 hnCommWord)))

@[expose] def hnPlain : List (List (Fin 7 × Bool)) :=
  hnRels0.mergeSort fun a b => decide (a.length ≤ b.length)


@[expose] def invChainWord (w : List Int) : List Int :=
  w.reverse.map fun z => if z % 2 == 0 then z + 1 else z - 1

@[expose] def hnTabImg : Array (List Int) :=
  let I := hnSpec.imgWords
  let a := I[0]!
  let b := I[1]!
  let c := I[2]!
  let d := I[3]!
  let t := I[4]!
  #[b, c ++ b ++ invChainWord c, c, d ++ c ++ d, a, d, t]

@[expose] def hnRelabel (z : Int) : Int :=
  let k : Int := match z.natAbs with
    | 1 => 5
    | 2 => 1
    | 3 => 3
    | 4 => 6
    | 5 => 7
    | _ => 0
  if 0 < z then k else -k

@[expose] def hnTabSurj : Array (List Int) := hnSpec.surjWords.map (·.map hnRelabel)

@[expose] def hnTabRels : List (List (Nat × Bool)) :=
  (hnRels ++ (List.finRange 7).map fun i => hnCommWord i ++ [(i, false)]).map
    (·.map fun l => (l.1.val, l.2))

@[expose] def hnTabSpec : Spec := ⟨7, hnTabRels, hnTabImg, hnTabSurj⟩

set_option compiler.extract_closed false in
@[expose] def hnTabCheck (_ : Unit) : Bool :=
  let D := CFSG.Sporadic.HN.Native.hnData
  let O := D.orbit ()
  wordChecks D.n hnTabSpec (slpLetters D.n (genT D.n O) D.words) O.alpha O.beta

end CFSG.Sporadic.Recognition.HNMultiplier

