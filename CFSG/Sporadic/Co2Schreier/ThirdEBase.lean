
module

public import CFSG.Sporadic.Co2Schreier.ThirdOrderBase
public import CFSG.Sporadic.Co2Schreier.Action
public import CFSG.Sporadic.Co2Schreier.CoresBase
public import CFSG.Sporadic.Co2Schreier.KernelBase
public import CFSG.Sporadic.Co2Schreier.SylowLemmas
public import CFSG.Sporadic.Schreier.RuSylowB
public import CFSG.Sporadic.Co2Schreier.ChainCheckInputs
public meta import CFSG.Sporadic.Co2Schreier.Arrays
public meta import Certificates.Data.CFSGNative.Schreier.Check
public import CFSG.Sporadic.Co2Schreier.TextCheckInputs
public meta import CFSG.Sporadic.Co2Schreier.Text
public import CFSG.Sporadic.Co2Schreier.ThirdCheckInputs
public meta import CFSG.Sporadic.Co2Schreier.WitCheck
public meta import CFSG.Sporadic.Co2Schreier.SylowCheckBase
public meta import CFSG.Sporadic.Co2Schreier.CoreCheckBase
public meta import CFSG.Sporadic.Co2Cert.FaithfulCheck
public import CFSG.Sporadic.Co2Cert.CheckInputs
public import CFSG.Sporadic.Co2Cert.OrderCheckInputs
public import CFSG.Sporadic.Schreier.RuLocal
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.Frattini.Core

@[expose] public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Sporadic.Co2Schreier

open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Certificates CFSG.Certificates.Native
  CFSG.Monster.B.Mathieu CFSG.Sporadic.Co2Cert CFSG.Sporadic.RuSchreier
  CFSG.Sporadic.SmallF2.Native

abbrev gA : Array (Array ℕ) := gArrsOf co2PosTable witRec

abbrev eRec : ChainRecord := eRecOf gA witRec

abbrev quA : Array (Array ℕ) := quArrsOf gA

abbrev quE : LeftEnum := leftEnum quA 1024

abbrev quP : Array (Array ℕ) := conjPis gA 1024 quE

abbrev quRec : ChainRecord := quRecOf quP

structure EFacts : Prop where
  len : ((oddMats witRec).length == 15) = true
  size : (gA.size == 15) = true
  wf : (oddMats witRec).all rows22OK = true
  gens : allLt 15 (fun i => isInvA 2300 gA[i]! (invCand 2300 gA[i]!) &&
      allLt 2300 (fun k => co2PackedVecs[(gA[i]!)[k]!]! ==
        vecMulN 22 (transposeRows 22 ((oddMats witRec).getD i []).toArray) co2PackedVecs[k]!) &&
      siftA 2300 (rawLevels 2300 co2StrongArrs co2BaseArr) co2BaseArr 0 gA[i]! &&
      eqA 2300 (compA 2300 gA[i]! uArr) (compA 2300 uArr gA[i]!)) = true
  eShape : chainShapeOK eRec 2300 15 26 witRec.third.baseIndices = true
  eOK : recordOK 2300 eRec 4 = true
  eOrb : (recordOrbits 2300 eRec == [20, 18, 32, 8, 4, 1, 2, 1, 1, 1, 1, 1, 2]) = true
  qu : allLt 10 (fun i => isInvA 2300 quA[i]! (invCand 2300 quA[i]!) &&
      eqA 2300 (compA 2300 quA[i]! quA[i]!) (idA 2300) &&
      allLt 10 (fun j => eqA 2300 (compA 2300 quA[i]! quA[j]!) (compA 2300 quA[j]! quA[i]!))) =
    true
  qEnum : enumOK quA 1024 quE = true
  qConj : conjOK gA quP 1024 quE = true
  qShape : chainShapeOK quRec 1024 15 17 [1, 2, 3, 4, 5, 6, 7, 8, 9, 10] = true
  qOK : recordOK 1024 quRec 4 = true
  qOrb : (recordOrbits 1024 quRec == [45, 16, 1, 2, 1, 1, 1, 1, 1, 1]) = true

def gPerm (i : ℕ) : Equiv.Perm (Fin 2300) := permOfArr 2300 gA[i]!

def gTuple : List (Equiv.Perm (Fin 2300)) := (List.range 15).map gPerm

theorem gTuple_length : gTuple.length = 15 := by simp [gTuple]

theorem gTuple_getD {i : ℕ} (hi : i < 15) : gTuple.getD i 1 = gPerm i := by
  rw [List.getD_eq_getElem _ _ (by rw [gTuple_length]; exact hi)]
  simp [gTuple]

def locE : Subgroup (Equiv.Perm (Fin 2300)) := Subgroup.closure {g | g ∈ gTuple}

theorem gPerm_mem_E {i : ℕ} (hi : i < 15) : gPerm i ∈ locE := by
  rw [← gTuple_getD hi]
  exact Subgroup.subset_closure (getD_mem (by rw [gTuple_length]; exact hi))

theorem eRec_origArrs : eRec.origArrs = gA := by
  simp [eRecOf, ChainRecord.origArrs, List.map_map, Function.comp_def]

theorem rep_powA {t : Array ℕ} {g : Equiv.Perm (Fin 2300)} (ht : Rep 2300 t g) :
    ∀ e, Rep 2300 (powA t e) (g ^ e)
  | 0 => by
    rw [powA, pow_zero]
    exact rep_idA
  | e + 1 => by
    rw [powA, pow_succ]
    exact rep_compA (rep_powA ht e) ht

def quPerm (i : ℕ) : Equiv.Perm (Fin 2300) := permOfArr 2300 quA[i]!

def quTuple : List (Equiv.Perm (Fin 2300)) := (List.range 10).map quPerm

theorem quTuple_length : quTuple.length = 10 := by simp [quTuple]

theorem quTuple_getD {i : ℕ} (hi : i < 10) : quTuple.getD i 1 = quPerm i := by
  rw [List.getD_eq_getElem _ _ (by rw [quTuple_length]; exact hi)]
  simp [quTuple]

theorem quA_size : quA.size = 10 := by simp [quA, quArrsOf, quRecipe]

def locQu : Subgroup (Equiv.Perm (Fin 2300)) := Subgroup.closure {g | g ∈ quTuple}

theorem mem_quTuple {x : Equiv.Perm (Fin 2300)} (hx : x ∈ quTuple) : ∃ i < 10, x = quPerm i := by
  obtain ⟨i, hi, rfl⟩ := (mem_iff_exists_getD (d := 1)).1 hx
  rw [quTuple_length] at hi
  exact ⟨i, hi, quTuple_getD hi⟩

theorem quRecipe_lt : ∀ r ∈ quRecipe, ∀ j ∈ r.1, j < 15 := by
  decide

theorem quA_get {i : ℕ} (hi : i < 10) :
    quA[i]! = powA (prodArr gA (quRecipe.getD i ([], 0)).1) (quRecipe.getD i ([], 0)).2 :=
  toArray_map_getElem! quRecipe _ ([], 0) (by simpa [quRecipe] using hi)

theorem quRec_origArrs : quRec.origArrs = quP := by
  simp [quRecOf, ChainRecord.origArrs, List.map_map, Function.comp_def]

end CFSG.Sporadic.Co2Schreier
