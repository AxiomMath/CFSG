module

public import Certificates.Data.NT44Model
public import Certificates.Data.NT44Commutator.Inputs
public import CFSG.Monster.B.Co2.PermArr
public import CFSG.Certificates.SchreierChainData
public import Mathlib.Logic.Equiv.Fin.Basic
public import Mathlib.Data.Vector.Basic
public import Mathlib.GroupTheory.Perm.Basic

public section

namespace CFSG.GH74.GLS.NT44.PermutationNative

open CFSG.Monster.B.Co2
open CFSG.Monster.B.Co2.Native
open CFSG.Certificates
open CFSG.Certificates.Native

@[expose] def step (tr : Array (Array Nat)) (i : Fin 256) (k : Fin 4) : Fin 256 :=
  if h : (tr[i.val]!)[k.val]! < 256 then ⟨(tr[i.val]!)[k.val]!, h⟩ else 0

@[expose] def walk (tr : Array (Array Nat)) (i : Fin 256) :
    List (SchreierLetter 4) → Fin 256
  | [] => i
  | (k, true) :: w => walk tr (step tr i k) w
  | (_, false) :: w => walk tr i w

@[expose] def mulIndex (tr : Array (Array Nat)) (parent : Array (List Int))
    (i j : Fin 256) : Fin 256 :=
  walk tr i (toLetters 4 parent[j.val]!)

@[expose] def powIndex (tr : Array (Array Nat)) (parent : Array (List Int))
    (i : Fin 256) : Nat → Fin 256
  | 0 => 0
  | n + 1 => mulIndex tr parent (powIndex tr parent i n) i

@[expose] def pairProducts (tr : Array (Array Nat)) (parent : Array (List Int))
    (i j : Fin 256) : List (Fin 256) :=
  List.ofFn (n := 16) fun q : Fin 16 =>
    let p : Fin 4 × Fin 4 := finProdFinEquiv.symm q
    mulIndex tr parent (powIndex tr parent i p.1.val) (powIndex tr parent j p.2.val)

abbrev Valid (tr : Array (Array Nat)) (parent : Array (List Int))
    (i j : Fin 256) : Prop :=
  mulIndex tr parent i j = mulIndex tr parent j i ∧
    powIndex tr parent i 4 = 0 ∧ powIndex tr parent i 2 ≠ 0 ∧
    powIndex tr parent j 4 = 0 ∧ powIndex tr parent j 2 ≠ 0 ∧
    (pairProducts tr parent i j).Nodup

@[expose] def p0InvArrays (D : NT44Inputs) : Array (Array Nat) :=
  D.p0.map (invCand 2688)

@[expose] def liftInvArrays (D : NT44Inputs) : Array (Array Nat) :=
  D.lifts.map (invCand 2688)

@[expose] def evalP0Word (D : NT44Inputs) (pi : Array (Array Nat))
    (w : List Int) : Array Nat :=
  wordA 2688 D.p0 pi w

@[expose] def alphaArray (D : NT44Inputs) (li : Array (Array Nat))
    (a : Fin 256) (c : Array Nat) : Array Nat :=
  compA 2688 (compA 2688 D.lifts[a.val]! c) li[a.val]!

@[expose] def termArray (D : NT44Inputs) (li : Array (Array Nat))
    (a : Fin 256) (c : Array Nat) : Array Nat :=
  compA 2688 (invCand 2688 c) (alphaArray D li a c)

@[expose] def witnessW (D : NT44Inputs) (li : Array (Array Nat))
    (W : CommutatorWitness) : Array Nat :=
  let c := evalP0Word D (p0InvArrays D) W.cWord
  let t := termArray D li W.aIndex c
  if W.sign then t else invCand 2688 t

abbrev DataOK (D : NT44Inputs) : Prop :=
  D.p0.size = 9 ∧ D.lifts.size = 256 ∧ D.ks.size = 2 ∧
    D.parent.size = 256 ∧ D.tr.size = 256 ∧
    (∀ i : Fin 256, (D.tr[i.val]!).size = 4 ∧
      ∀ k : Fin 4, (D.tr[i.val]!)[k.val]! < 256) ∧
    positiveWordsOK D.parent = true

abbrev ActorSetsOK (A : Array (List (Fin 256))) : Prop :=
  A.size = 3 ∧ ∀ a : Fin 3, (A[a.val]!).Nodup ∧ (A[a.val]!).length = 16

abbrev PairActorOK (tr : Array (Array Nat)) (parent : Array (List Int))
    (A : Array (List (Fin 256))) : Prop :=
  ∀ i j : Fin 256, Valid tr parent i j →
    ∃ a : Fin 3, (pairProducts tr parent i j).Perm (A[a.val]!)

abbrev WitnessOK (D : NT44Inputs) (li : Array (Array Nat))
    (actorSet : List (Fin 256)) (W : CommutatorWitness) : Prop :=
  W.sIndex ∈ actorSet ∧ W.aIndex ∈ actorSet ∧
    lettersOK 9 W.cWord = true ∧
    mulIndex D.tr D.parent W.sIndex W.sIndex = 0 ∧
    W.sIndex ≠ 0 ∧
    let c := evalP0Word D (p0InvArrays D) W.cWord
    let t := termArray D li W.aIndex c
    let s := D.lifts[W.sIndex.val]!
    let w := witnessW D li W
    isInvA 2688 c (invCand 2688 c) = true ∧
    isInvA 2688 t (invCand 2688 t) = true ∧
    eqA 2688 (compA 2688 (compA 2688 s c) (invCand 2688 s)) c = true ∧
      eqA 2688 (compA 2688 w w) (idA 2688) = true ∧
      eqA 2688 w (idA 2688) = false ∧
      eqA 2688 (compA 2688 w D.ks[0]!) (compA 2688 D.ks[0]! w) = true ∧
      eqA 2688 (compA 2688 w D.ks[1]!) (compA 2688 D.ks[1]! w) = true

abbrev CommutatorCheckProp (D : NT44Inputs)
    (A : Array (List (Fin 256))) (W : Array CommutatorWitness) : Prop :=
  DataOK D ∧ ActorSetsOK A ∧ W.size = 3 ∧
    (∀ a : Fin 3, WitnessOK D (liftInvArrays D) (A[a.val]!) (W[a.val]!)) ∧
    PairActorOK D.tr D.parent A



@[expose] def commutatorCheck (_ : Unit := ()) : Bool :=
  let D := PermutationNative.inputs ()
  decide (CommutatorCheckProp D (actorSets ()) (witnesses ()))

theorem commutatorCheck_spec (h : commutatorCheck () = true) :
    CommutatorCheckProp (PermutationNative.inputs ())
      (actorSets ()) (witnesses ()) := by
  unfold commutatorCheck at h
  exact of_decide_eq_true h

end CFSG.GH74.GLS.NT44.PermutationNative
