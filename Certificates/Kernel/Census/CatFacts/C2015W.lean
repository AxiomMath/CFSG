module

public import Certificates.Data.Kernel.Census.CatFacts.C2015Defs
public import Certificates.Kernel.Census.CatFacts.C2015Wit
import CFSG.Certificates.Kernel.Census.CatFacts.PkWordSound

public section

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace CFSG.Certificates.Kernel.CatFacts

open CFSG.ComponentClassification.CatFactsSmall.PSp43 CFSG.Certificates.Kernel.PkEnum
  CFSG.Sporadic.Schreier

theorem pkp_prodW {n : Nat} (w : List (VP n)) : pkp (prodW w) = pkpW w := by
  induction w with
  | nil => exact pkp_oneV n
  | cons a w ih => rw [prodW, List.foldr_cons, ← prodW, pkp_mulV, ih, pkpW_cons]

theorem pkp_cubeV {n : Nat} (u : VP n) : pkp (cubeV u) = pkp u ^ 3 := by
  rw [cubeV, forceV_eq, pkp_mulV, pkp_mulV, pow_succ', pow_succ', pow_one]

theorem pkp_pow45 {n : Nat} (u : VP n) : pkp (pow45 u) = pkp u ^ 45 := by
  rw [pow45, forceV_eq, pkp_mulV, pkp_mulV, pkp_mulV, pkp_mulV, pkp_cubeV, pkp_cubeV,
    show 45 = 3 * 3 * 5 by rfl, pow_mul, pow_mul]
  generalize (pkp u ^ 3) ^ 3 = d
  rw [pow_succ', pow_succ', pow_succ', pow_succ', pow_one]

@[expose] def four1V {n : Nat} (u : VP n) : Bool :=
  forceV (mulV u u) fun q => isOneW [mulV q q]

@[expose] def comm4W {n : Nat} (y : List (VP n)) : Bool :=
  forceV (prodW y) fun p => !isOneW [p] && four1V p

@[expose] def oddTW {n : Nat} (T : List (List (VP n))) (is : List Nat) (x : List (VP n)) : Bool :=
  match pickW T is with
  | some c => comm4W (x ++ c ++ invW x ++ invW c)
  | none => false

@[expose] def oddScanW {n : Nat} (T : List (List (VP n))) :
    List (List Nat) → List (List (VP n)) → Bool
  | _, [] => true
  | ws, x :: l => match four1V (prodW x), ws with
    | true, ws => oddScanW T ws l
    | false, [] => false
    | false, is :: ws => oddTW T is x && oddScanW T ws l

theorem isOneW_pow45_of_four {n : Nat} {u : VP n} (h4 : four1V u = true) :
    isOneW [pow45 u] = isOneW [u] := by
  rw [four1V, forceV_eq, isOneW_eq, pkpW_single, pkp_mulV, pkp_mulV, decide_eq_true_eq] at h4
  have h4' : pkp u ^ 4 = 1 := by
    rw [← h4, pow_succ, pow_succ, pow_succ, pow_one, mul_assoc (pkp u * pkp u)]
  have e : (45 : Nat) = 4 * 11 + 1 := rfl
  have h45 : pkp u ^ 45 = pkp u := by
    rw [e, pow_succ, pow_mul, h4', one_pow, one_mul]
  rw [isOneW_eq, isOneW_eq, pkpW_single, pkpW_single, pkp_pow45, h45]

theorem isOneW_prodW {n : Nat} (w : List (VP n)) : isOneW [prodW w] = isOneW w := by
  rw [isOneW_eq, isOneW_eq, pkpW_single, pkp_prodW]

theorem oddScanW_sound {n : Nat} (T : List (List (VP n))) : ∀ (ws : List (List Nat))
    (l : List (List (VP n))), oddScanW T ws l = true →
    l.all (fun x => isOneW x || !isOneW [pow45 (prodW x)] ||
      (productsW T).any fun c => !isOneW [pow45 (prodW (x ++ c ++ invW x ++ invW c))]) = true
  | _, [], _ => rfl
  | ws, x :: l, h => by
    rw [List.all_cons, Bool.and_eq_true]
    cases h4 : four1V (prodW x)
    · cases ws with
      | nil => simp only [oddScanW, h4, Bool.false_eq_true] at h
      | cons is ws =>
        simp only [oddScanW, h4, Bool.and_eq_true] at h
        refine ⟨?_, oddScanW_sound T ws l h.2⟩
        have h1 := h.1
        unfold oddTW at h1
        split at h1
        · rename_i c hc
          unfold comm4W at h1
          rw [forceV_eq, Bool.and_eq_true] at h1
          rw [Bool.or_eq_true]
          refine Or.inr (List.any_eq_true.2 ⟨c, pickW_mem T is c hc, ?_⟩)
          rw [isOneW_pow45_of_four h1.2]
          exact h1.1
        · exact absurd h1 Bool.false_ne_true
    · simp only [oddScanW, h4] at h
      refine ⟨?_, oddScanW_sound T ws l h⟩
      rw [isOneW_pow45_of_four h4, isOneW_prodW]
      cases isOneW x <;> rfl

@[expose] def wit2015L : List (List Nat) :=
  [[0, 2], [0, 1], [0, 2], [0, 1], [0, 1], [0, 1], [0, 1], [0, 1], [0, 1], [0, 2], [0, 1], [0, 2],
    [2, 0], [0, 2], [3, 1], [0, 2], [3, 3], [0, 5], [0, 5], [0, 1], [0, 5], [0, 1], [0, 5], [0, 1],
    [0, 1], [0, 1], [0, 1], [0, 1], [1, 8], [0, 1], [1, 2], [1, 4], [0, 5], [0, 2], [0, 5], [0, 5],
    [0, 5], [0, 2], [0, 5], [0, 7], [0, 7], [0, 6], [0, 2], [0, 2], [1, 0], [0, 2], [1, 0], [1, 1],
    [0, 6], [1, 1], [1, 0], [0, 2], [1, 0], [0, 1], [0, 6], [0, 1], [1, 1], [1, 3], [0, 2], [0, 6],
    [0, 2], [1, 0], [0, 2], [0, 11], [0, 11], [0, 2], [0, 1], [0, 1], [0, 1], [0, 1], [1, 0], [0, 6],
    [0, 6], [1, 3], [1, 1], [0, 2], [0, 2], [0, 7], [0, 7], [0, 7], [0, 1], [0, 5], [0, 1], [0, 6],
    [0, 11], [0, 5], [0, 7], [0, 11], [0, 5], [0, 5], [0, 7], [0, 7], [0, 1], [0, 7], [0, 1], [0, 6],
    [0, 2], [1, 1], [0, 2], [0, 6], [1, 3], [0, 1], [1, 0], [0, 1], [0, 2], [1, 0], [0, 2], [0, 6],
    [1, 3], [1, 1], [0, 6], [0, 1], [0, 1], [0, 1], [0, 1], [0, 11], [0, 2], [0, 11], [0, 2], [1, 0],
    [1, 0], [0, 2], [1, 0], [0, 1], [1, 0], [0, 1], [1, 2], [1, 1], [0, 11], [0, 7], [0, 5], [0, 11],
    [0, 6], [0, 5], [0, 2], [0, 7], [0, 7], [0, 6], [0, 5], [0, 2], [0, 5], [0, 5], [0, 5], [0, 5],
    [0, 2], [0, 2], [0, 1], [0, 1], [1, 0], [1, 1], [0, 6], [1, 1], [1, 0], [1, 0], [1, 0], [1, 0],
    [1, 0], [1, 0], [1, 1], [1, 0], [0, 2], [0, 1], [1, 2], [0, 1], [3, 3], [0, 1], [0, 2], [0, 2],
    [0, 2], [3, 1], [0, 2], [0, 1], [2, 0], [1, 8], [1, 4], [1, 2], [0, 1], [0, 1], [0, 1], [0, 1],
    [0, 1], [0, 1], [0, 1], [1, 0], [0, 1], [1, 0], [1, 2], [0, 2], [1, 0], [1, 1], [1, 0], [0, 5],
    [0, 5], [0, 5], [0, 5], [0, 1], [0, 1], [1, 0], [1, 1], [1, 0], [1, 2], [1, 0], [1, 0], [0, 2],
    [0, 1], [0, 1], [0, 1], [0, 1], [1, 0], [1, 1], [0, 6], [1, 1], [1, 0], [1, 1], [1, 1], [1, 1],
    [0, 2], [1, 1], [1, 1], [0, 6], [1, 1], [1, 0], [0, 2], [1, 0]]

theorem oddScan2015K :
    (forceLL (transL QL45) fun T => oddScanW T wit2015L (productsW T)) = true := by
  decide +kernel

theorem oddN2015K : oddNW = true := by
  have h := oddScan2015K
  rw [forceLL_eq] at h
  unfold oddNW
  rw [forceLL_eq]
  exact oddScanW_sound _ _ _ h

theorem range45_split : List.range 45 = List.range' 0 5 ++ List.range' 5 5 ++ List.range' 10 5 ++
    List.range' 15 5 ++ List.range' 20 5 ++ List.range' 25 5 ++ List.range' 30 5 ++
    List.range' 35 5 ++ List.range' 40 5 := by
  decide

theorem cenA2015_0 : ((List.range' 0 5).map fun j => ((blockW lit2015A j).filter fun w =>
    eqW (w ++ [lit2015S]) (lit2015S :: w)).length).sum = 192 := by
  decide +kernel

theorem cenA2015_1 : ((List.range' 5 5).map fun j => ((blockW lit2015A j).filter fun w =>
    eqW (w ++ [lit2015S]) (lit2015S :: w)).length).sum = 192 := by
  decide +kernel

theorem cenA2015_2 : ((List.range' 10 5).map fun j => ((blockW lit2015A j).filter fun w =>
    eqW (w ++ [lit2015S]) (lit2015S :: w)).length).sum = 144 := by
  decide +kernel

theorem cenA2015_3 : ((List.range' 15 5).map fun j => ((blockW lit2015A j).filter fun w =>
    eqW (w ++ [lit2015S]) (lit2015S :: w)).length).sum = 0 := by
  decide +kernel

theorem cenA2015_4 : ((List.range' 20 5).map fun j => ((blockW lit2015A j).filter fun w =>
    eqW (w ++ [lit2015S]) (lit2015S :: w)).length).sum = 144 := by
  decide +kernel

theorem cenA2015_5 : ((List.range' 25 5).map fun j => ((blockW lit2015A j).filter fun w =>
    eqW (w ++ [lit2015S]) (lit2015S :: w)).length).sum = 192 := by
  decide +kernel

theorem cenA2015_6 : ((List.range' 30 5).map fun j => ((blockW lit2015A j).filter fun w =>
    eqW (w ++ [lit2015S]) (lit2015S :: w)).length).sum = 144 := by
  decide +kernel

theorem cenA2015_7 : ((List.range' 35 5).map fun j => ((blockW lit2015A j).filter fun w =>
    eqW (w ++ [lit2015S]) (lit2015S :: w)).length).sum = 240 := by
  decide +kernel

theorem cenA2015_8 : ((List.range' 40 5).map fun j => ((blockW lit2015A j).filter fun w =>
    eqW (w ++ [lit2015S]) (lit2015S :: w)).length).sum = 192 := by
  decide +kernel

theorem cenP2015_0 : ((List.range' 0 5).map fun j => ((blockW lit2015P j).filter fun w =>
    eqW (w ++ [lit2015S]) (lit2015S :: w)).length).sum = 96 := by
  decide +kernel

theorem cenP2015_1 : ((List.range' 5 5).map fun j => ((blockW lit2015P j).filter fun w =>
    eqW (w ++ [lit2015S]) (lit2015S :: w)).length).sum = 24 := by
  decide +kernel

theorem cenP2015_2 : ((List.range' 10 5).map fun j => ((blockW lit2015P j).filter fun w =>
    eqW (w ++ [lit2015S]) (lit2015S :: w)).length).sum = 72 := by
  decide +kernel

theorem cenP2015_3 : ((List.range' 15 5).map fun j => ((blockW lit2015P j).filter fun w =>
    eqW (w ++ [lit2015S]) (lit2015S :: w)).length).sum = 96 := by
  decide +kernel

theorem cenP2015_4 : ((List.range' 20 5).map fun j => ((blockW lit2015P j).filter fun w =>
    eqW (w ++ [lit2015S]) (lit2015S :: w)).length).sum = 72 := by
  decide +kernel

theorem cenP2015_5 : ((List.range' 25 5).map fun j => ((blockW lit2015P j).filter fun w =>
    eqW (w ++ [lit2015S]) (lit2015S :: w)).length).sum = 96 := by
  decide +kernel

theorem cenP2015_6 : ((List.range' 30 5).map fun j => ((blockW lit2015P j).filter fun w =>
    eqW (w ++ [lit2015S]) (lit2015S :: w)).length).sum = 72 := by
  decide +kernel

theorem cenP2015_7 : ((List.range' 35 5).map fun j => ((blockW lit2015P j).filter fun w =>
    eqW (w ++ [lit2015S]) (lit2015S :: w)).length).sum = 96 := by
  decide +kernel

theorem cenP2015_8 : ((List.range' 40 5).map fun j => ((blockW lit2015P j).filter fun w =>
    eqW (w ++ [lit2015S]) (lit2015S :: w)).length).sum = 96 := by
  decide +kernel

theorem cnt2015K : cnt2015 = (45, 45, 1440, 720) := by
  unfold cnt2015
  simp only [forceLL_eq, forceV_eq]
  rw [lit2015A_eq, lit2015P_eq, lit2015S_eq, range45_split]
  simp only [List.map_append, List.sum_append]
  rw [cenA2015_0, cenA2015_1, cenA2015_2, cenA2015_3, cenA2015_4, cenA2015_5, cenA2015_6,
    cenA2015_7, cenA2015_8, cenP2015_0, cenP2015_1, cenP2015_2, cenP2015_3, cenP2015_4, cenP2015_5,
    cenP2015_6, cenP2015_7, cenP2015_8]
  decide +kernel

end CFSG.Certificates.Kernel.CatFacts
