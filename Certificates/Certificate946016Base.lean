module

public import Certificates.Data.ParrottPSp43

@[expose] public section

namespace CFSG.RankThree.GF2n.Parrott

open CFSG.ComponentClassification.CatFactsSmall.PSp43
open CFSG.GH74.KGroups

local notation "P45" => Equiv.Perm (Fin 45)

@[expose] def o3a : P45 := sigma1

@[expose] def o3b : P45 :=
  List.formPerm [0, 3, 6] * List.formPerm [1, 5, 7] * List.formPerm [2, 4, 8] *
  List.formPerm [9, 15, 12] * List.formPerm [10, 25, 13] * List.formPerm [11, 35, 14] *
  List.formPerm [17, 26, 19] * List.formPerm [18, 36, 22] * List.formPerm [20, 27, 29] *
  List.formPerm [21, 37, 32] * List.formPerm [23, 28, 39] * List.formPerm [24, 38, 42] *
  List.formPerm [31, 40, 33] * List.formPerm [34, 41, 43]

@[expose] def o3c : P45 :=
  List.formPerm [0, 5, 8] * List.formPerm [1, 4, 6] * List.formPerm [2, 3, 7] *
  List.formPerm [9, 15, 13] * List.formPerm [10, 25, 14] * List.formPerm [11, 35, 12] *
  List.formPerm [16, 21, 39] * List.formPerm [17, 31, 42] * List.formPerm [18, 41, 36] *
  List.formPerm [20, 29, 22] * List.formPerm [23, 30, 32] * List.formPerm [24, 40, 26] *
  List.formPerm [27, 34, 43] * List.formPerm [28, 44, 37]

@[expose] def o3Gens : List P45 := [o3a, o3b, o3c]

@[expose] def o3Steps : List P45 := o3Gens ++ o3Gens.map Inv.inv

@[expose] def closeStep (S steps : List P45) : List P45 :=
  (S ++ (S.product steps).map (fun p => p.1 * p.2)).eraseDups

@[expose] def closeFuel (steps : List P45) : Nat → List P45 → List P45
  | 0, S => S
  | n + 1, S => closeFuel steps n (closeStep S steps)

@[expose] def O3 (_ : Unit := ()) : List P45 := closeFuel o3Steps 6 [1]

@[expose] def centralizerSigma1 : List P45 :=
  (elemsT QA45).filter fun c => c * sigma1 == sigma1 * c

@[expose] def classInO3 (g : P45) (_ : Unit := ()) : Finset P45 :=
  (((elemsT QA45).map fun c => c * g * c⁻¹).filter fun x => decide (x ∈ O3 ())).toFinset

@[expose] def classCentralizerSize (g : P45) (_ : Unit := ()) : Nat :=
  ((elemsT QA45).filter fun c => c * g * c⁻¹ == g).length

@[expose] def o3CenterComplement (_ : Unit := ()) : Finset P45 :=
  ((O3 ()).filter fun x => decide (x ∉ ({1, sigma1, sigma1 * sigma1} : Finset P45))).toFinset

structure ParrottO3Facts : Prop where
  o3_nodup : (O3 ()).Nodup
  o3_length : (O3 ()).length = 27
  o3_one_mem : (1 : P45) ∈ O3 ()
  o3_mul_closed :
    (O3 ()).all (fun x => (O3 ()).all (fun y => decide (x * y ∈ O3 ()))) = true
  o3_inv_closed : (O3 ()).all (fun x => decide (x⁻¹ ∈ O3 ())) = true
  o3_fixed : closeStep (O3 ()) o3Steps = O3 ()
  o3a_mem : o3a ∈ O3 ()
  o3b_mem : o3b ∈ O3 ()
  o3c_mem : o3c ∈ O3 ()
  o3a_cube : o3a ^ 3 = 1
  o3b_cube : o3b ^ 3 = 1
  o3c_cube : o3c ^ 3 = 1
  O3_le_QA45 : (O3 ()).all (fun x => QA45.sift x 0) = true
  isHeisenberg_O3 :
    ((O3 ()).all (fun x => decide (x ^ 3 = 1)) = true) ∧
      ((O3 ()).any (fun x => (O3 ()).any (fun y => decide (x * y ≠ y * x))) = true)
  center_O3 :
    ((O3 ()).filter fun x => (O3 ()).all (fun y => decide (x * y = y * x))).toFinset =
      ({1, sigma1, sigma1 * sigma1} : Finset P45)
  sigma1_mem_O3 : sigma1 ∈ O3 ()
  sigma2inv_not_mem_O3 : sigma1 * sigma2⁻¹ ∉ O3 ()
  O3_le_centralizer_sigma1 : (O3 ()).all (fun x => decide (x * sigma1 = sigma1 * x)) = true
  O3_normal_in_centralizer :
    centralizerSigma1.length = 648 ∧
      centralizerSigma1.all (fun c =>
        (O3 ()).all (fun x => decide (c * x * c⁻¹ ∈ O3 ()))) = true
  class_of_sigma1sigma2inv :
    classCentralizerSize (sigma1 * sigma2⁻¹) () = 108 ∧
      51840 / classCentralizerSize (sigma1 * sigma2⁻¹) () = 480 ∧
      classInO3 (sigma1 * sigma2⁻¹) () = o3CenterComplement ()

end CFSG.RankThree.GF2n.Parrott

