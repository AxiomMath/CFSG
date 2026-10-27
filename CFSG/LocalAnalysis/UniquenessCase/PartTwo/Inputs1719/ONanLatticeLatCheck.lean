module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.ONanLatticeLatData
public import CFSG.Sporadic.Schreier.ONOuterData

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

@[expose] def onl_chk (A B : Nat) : List Nat → Nat → Bool
  | [], _ => true
  | a :: t, p => (A.testBit p == B.testBit a) && onl_chk A B t (p + 1)

@[expose] def onl_chk2 (A B A' B' : Nat) (t : List Nat) : Bool :=
  onl_chk A A' t 0 && onl_chk B B' t 0

@[expose] def onl_chkConj (r u : List Nat) : List Nat → Nat → Bool
  | [], _ => true
  | a :: t, x => (r.getD (u.getD x 0) 0 == u.getD a 0) && onl_chkConj r u t (x + 1)

@[expose] def onl_comp (t u : List Nat) : List Nat := u.map fun y => t.getD y 0

@[expose] def onl_genT (a : Nat) : List Nat :=
  if a = 0 then onl_r0 else if a = 1 then onl_r1
  else (CFSG.ONSchreier.Data.PSL120Chain.generators[a - 2]!).toList

@[expose] def onl_wordT : List Nat → List Nat
  | [] => List.range 120
  | a :: w => onl_comp (onl_genT a) (onl_wordT w)

@[expose] def onl_J : List Nat := [0, 1, 2, 3, 6, 7]

@[expose] def onl_tgenT (j : Nat) : List Nat :=
  if j < 6 then (CFSG.ONSchreier.Data.PSL120Chain.generators[onl_J.getD j 0]!).toList
  else onl_tauT

@[expose] def onl_kgenT (i j : Nat) : List Nat := if j < 7 then onl_tgenT j else onl_gT.getD i []

@[expose] def onl_A (k : Nat) : Nat := onl_LA.getD k 0

@[expose] def onl_B (k : Nat) : Nat := onl_LB.getD k 0

@[expose] def onl_mapsTo (t : List Nat) (k l : Nat) : Bool :=
  onl_chk2 (onl_A k) (onl_B k) (onl_A l) (onl_B l) t

theorem onl_conj_check :
    onl_chkConj onl_r0 CFSG.ONSchreier.Data.quotientConjugator.toList
        (CFSG.ONSchreier.Data.M120Chain.generators[0]!).toList 0 = true ∧
      onl_chkConj onl_r1 CFSG.ONSchreier.Data.quotientConjugator.toList
        (CFSG.ONSchreier.Data.M120Chain.generators[1]!).toList 0 = true ∧
      onl_r0.length = 120 ∧ onl_r1.length = 120 ∧
      CFSG.ONSchreier.Data.quotientConjugator.size = 120 ∧
      (CFSG.ONSchreier.Data.M120Chain.generators[0]!).size = 120 ∧
      (CFSG.ONSchreier.Data.M120Chain.generators[1]!).size = 120 := by
  decide +kernel

theorem onl_word_check : onl_wordT onl_tauW = onl_tauT ∧
    (List.range 8).all (fun i => onl_wordT (onl_gW.getD i []) == onl_gT.getD i []) = true ∧
    onl_tauW.all (· < 14) = true ∧ onl_gW.all (fun w => w.all (· < 14)) = true ∧
    onl_gW.length = 8 ∧ onl_gT.length = 8 := by
  decide +kernel

theorem onl_tree_check : onl_LA.length = 315 ∧ onl_LB.length = 315 ∧ onl_Lt.length = 315 ∧
    onl_Lc.length = 315 ∧ onl_A 0 = onl_mO ∧ onl_B 0 = onl_mD ∧
    (List.range 315).all (fun k => decide (onl_A k < 2 ^ 120) && decide (onl_B k < 2 ^ 120)) =
      true ∧
    (List.range 315).all (fun k => k == 0 || (decide ((onl_Lt.getD k (0, 0)).1 < k) &&
      decide ((onl_Lt.getD k (0, 0)).2 < 2) &&
      onl_mapsTo (if (onl_Lt.getD k (0, 0)).2 = 0 then onl_r0 else onl_r1)
        (onl_Lt.getD k (0, 0)).1 k)) = true := by
  decide +kernel

theorem onl_closure_check :
    (List.range 315).all (fun k => decide ((onl_Lc.getD k (0, 0)).1 < 315) &&
      decide ((onl_Lc.getD k (0, 0)).2 < 315) &&
      onl_mapsTo onl_r0 k (onl_Lc.getD k (0, 0)).1 &&
      onl_mapsTo onl_r1 k (onl_Lc.getD k (0, 0)).2) = true := by
  decide +kernel

theorem onl_nodup_check :
    ((List.range 315).map fun k => onl_A k + 2 ^ 120 * onl_B k).Nodup := by
  decide +kernel

theorem onl_forest_check :
    onl_F.length = 315 ∧ onl_reps.length = 10 ∧ onl_reps.getD 0 0 = 0 ∧
    onl_A (onl_reps.getD 9 0) = onl_mO ∧ onl_reps.all (· < 315) = true ∧
    (List.range 315).all (fun k =>
      if onl_reps.contains k then (onl_F.getD k (0, 0, 0)).2.2 == 0
      else decide ((onl_F.getD k (0, 0, 0)).1 < 315) &&
        decide ((onl_F.getD (onl_F.getD k (0, 0, 0)).1 (0, 0, 0)).2.2 <
          (onl_F.getD k (0, 0, 0)).2.2) &&
        decide ((onl_F.getD k (0, 0, 0)).2.1 < 7) &&
        onl_mapsTo (onl_tgenT (onl_F.getD k (0, 0, 0)).2.1) (onl_F.getD k (0, 0, 0)).1 k) =
      true ∧
    (List.range 8).all (fun i => onl_chk2 onl_mO onl_mD (onl_A (onl_reps.getD (i + 1) 0))
      (onl_B (onl_reps.getD (i + 1) 0)) (onl_gT.getD i [])) = true ∧
    (List.range 7).all (fun j => onl_chk2 onl_mO onl_mD onl_mO onl_mD (onl_tgenT j)) = true ∧
    (List.range 7).all (fun j => (onl_tgenT j).length == 120) = true ∧
    (List.range 8).all (fun i => (onl_gT.getD i []).length == 120) = true ∧
    onl_tauT.length = 120 := by
  decide +kernel

theorem onl_k5_check : onl_K5.length = 8 ∧ (List.range 8).all (fun i =>
    (onl_K5.getD i []).length == 315 && ((onl_K5.getD i []).getD 0 (0, 0, 0)).1 == 0 &&
    (List.range 315).all (fun k => ((onl_K5.getD i []).map (·.1)).contains k) &&
    (List.range 315).all (fun t => t == 0 ||
      (decide (((onl_K5.getD i []).getD t (0, 0, 0)).2.1 < t) &&
      decide (((onl_K5.getD i []).getD t (0, 0, 0)).2.2 < 8) &&
      decide (((onl_K5.getD i []).getD t (0, 0, 0)).1 < 315) &&
      onl_mapsTo (onl_kgenT i ((onl_K5.getD i []).getD t (0, 0, 0)).2.2)
        ((onl_K5.getD i []).getD ((onl_K5.getD i []).getD t (0, 0, 0)).2.1 (0, 0, 0)).1
        ((onl_K5.getD i []).getD t (0, 0, 0)).1))) = true := by
  decide +kernel

theorem onl_misc_check : (List.range 14).all (fun a => (onl_genT a).length == 120) = true ∧
    (List.range 315).filter (fun k => onl_A k == onl_mO) = [0, 48, 122] := by
  decide +kernel

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
