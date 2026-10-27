module

public import CFSG.Sporadic.Co1.Module.Pairs
public import CFSG.Sporadic.Co1.Module.Involutions
public import CFSG.Sporadic.Co1.Module.InvAssemble
public import CFSG.Monster.GMS.Facts.Co1OddPairs
public import CFSG.Monster.GMS.Leech.Linear
public import CFSG.Monster.GMS.S365RootInputs
public import Certificates.Kernel.Co1Cover.Bridge
public import Certificates.Kernel.Co1M.Orb98280
public import Certificates.Kernel.Co1M.Data10044
public import CFSG.Certificates.Kernel.Co1M.BfsTreeSound
public import Certificates.Kernel.Co1M.Cov10044
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelCo1M

open CFSG.KC.Co1F2 CFSG.KC.M1F2 CFSG.KC.Loop CFSG.KC.BfsT CFSG.KC.Co1M CFSG.KC.VecK CFSG.KD.Co1M
  CFSG.Sporadic.SmallF2.Native CFSG.Sporadic.Co1.InvNative CFSG.Sporadic.Co1.Module
  CFSG.Sporadic.Co1.Module.Pairs CertificateChecks.KernelCo1Cover

theorem strictN_eq44 (y : Nat) (k : Nat → Nat) : strictN y k = k y := by
  cases y <;> rfl

theorem mulU44 (A B : Nat) :
    mulRows 24 (unpackR 24 A) (unpackR 24 B) = unpackR 24 (mulF 24 A B) :=
  mul_sound (Nat.beq_refl _)

theorem idU44 : idRows 24 = unpackR 24 (idF 24) := by decide +kernel

theorem letterU44 (b : Bool) :
    letterRows b = unpackR 24 (Bool.rec (motive := fun _ => Nat) R1 R0 b) := by
  cases b
  · exact rowsB_eq
  · exact rowsA_eq

theorem wordU44 (w : List Bool) (acc : Nat) :
    w.foldl (fun a b => mulRows 24 a (letterRows b)) (unpackR 24 acc) =
      unpackR 24 (wordFA R0 R1 w acc) := by
  induction w generalizing acc with
  | nil => rfl
  | cons b w ih =>
    rw [List.foldl_cons, letterU44, mulU44, ih]
    exact congrArg (unpackR 24)
      (strictN_eq44 (mulF 24 acc (Bool.rec (motive := fun _ => Nat) R1 R0 b)) (wordFA R0 R1 w)).symm

theorem wordRowsU (w : List Bool) : wordRows w = unpackR 24 (wordF R0 R1 w) := by
  rw [wordRows, idU44, wordU44]
  rfl

theorem gwU44 (a b : Nat) (w : List Nat) (hw : ∀ l ∈ w, l < 2) (acc : Nat) :
    w.foldl (fun x l => mulRows 24 x (#[unpackR 24 a, unpackR 24 b])[l]!) (unpackR 24 acc) =
      unpackR 24 (gwFA [a, b] w acc) := by
  induction w generalizing acc with
  | nil => rfl
  | cons l w ih =>
    have hl : (#[unpackR 24 a, unpackR 24 b])[l]! = unpackR 24 (getL 0 [a, b] l) := by
      have h2 : l < 2 := hw l (by simp)
      rcases (by omega : l = 0 ∨ l = 1) with rfl | rfl <;> rfl
    rw [List.foldl_cons, hl, mulU44, ih (fun l h => hw l (List.mem_cons_of_mem _ h))]
    exact congrArg (unpackR 24) (strictN_eq44 (mulF 24 acc (getL 0 [a, b] l)) (gwFA [a, b] w)).symm

theorem powU44 (M : Nat) : ∀ e, powRows 24 (unpackR 24 M) e = unpackR 24 (powK 24 M e)
  | 0 => idU44
  | e + 1 => by
    rw [powRows, powU44 M e, mulU44]
    exact congrArg (unpackR 24) (strictN_eq44 (powK 24 M e) fun a => mulF 24 a M).symm

theorem rowsSA_eq : rowsSA = unpackR 24 SA := by
  have hw : ∀ l ∈ wordA, l < 2 := by decide
  unfold rowsSA genWordRows kGens
  rw [wordRowsU, wordRowsU, idU44, gwU44 _ _ _ hw, powU44]
  exact congrArg (unpackR 24) (Nat.eq_of_beq_eq_true (by quickRfl))

theorem conjRows_eq (w : List Bool) : conjRows w = unpackR 24
    (mulF 24 SA (mulF 24 (mulF 24 (wordF R0 R1 w) SA) (wordF R0 R1 (invWordL w)))) := by
  rw [Pairs.conjRows, rowsSA_eq, wordRowsU, wordRowsU, mulU44, mulU44, mulU44]

theorem rootRows1_eq : rootRows1 = unpackR 24 C1 := by
  rw [rootRows1, conjRows_eq, powU44]
  exact congrArg (unpackR 24) (Nat.eq_of_beq_eq_true (by quickRfl))

theorem rootRows2_eq : rootRows2 = unpackR 24 C2 := by
  rw [rootRows2, conjRows_eq, powU44, wordRowsU, mulU44]
  exact congrArg (unpackR 24) (Nat.eq_of_beq_eq_true (by quickRfl))

theorem bfs10044 : bfsTree (mclAct (unpackR 24 C1) (unpackR 24 C2)) rootBase 400 =
    (TL.toArray, TP.toArray, TB.toArray) :=
  bfsTree_sound (by quickRfl)

theorem cover10044 : coverOK (orbitOf 2 98280) rootGs TL.toArray = true := by
  unfold coverOK
  rw [List.all_eq_true]
  intro p hp
  rw [List.mem_range] at hp
  have e : (orbitOf 2 98280).pts[p]! = lk CertificateChecks.KernelVec.Co1.Pt 32 p :=
    cm_orb_twin.2.1 p hp
  rw [e, List.contains_toArray]
  exact cov44All p hp

theorem c10044_root : rootCheck = true := by
  unfold rootCheck rootCheckT
  rw [rootRows1_eq, rootRows2_eq, bfs10044]
  dsimp only
  rw [rowsSA_eq, cover10044, Bool.and_true]
  quickRfl

theorem c10044_neg :
    (!bfsK (mclAct (unpackR 24 C1) (unpackR 24 C2)) rootBase 400 TL (TP.set 5 0) TB &&
      !bfsK (mclAct (unpackR 24 C1) (unpackR 24 C2)) rootBase 100 TL TP TB &&
      !(!orthAll rootGs (lk CertificateChecks.KernelVec.Co1.Pt 32 827) ||
        ([] : List Nat).contains (lk CertificateChecks.KernelVec.Co1.Pt 32 827))) = true := by
  quickRfl

open Certificates in
open CFSG.Sporadic.Co1.Module.Pairs in
theorem c10044 :
    rootCheck = true := c10044_root

end CertificateChecks.KernelCo1M

end
