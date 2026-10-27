module

public import CFSG.Sporadic.Schreier.MathieuOddCoreM22Outer
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListM22DataInputs

public section

namespace CFSG.Quasithin.H13.S126M22

open Equiv CFSG.QuasithinUnique.Vol2Native.A312L CFSG.QuasithinUnique.Vol2Native.A312L.M22Lat
  PermLat CFSG.Sporadic.Schreier CFSG.Sporadic.Mathieu

@[expose] def g0 : Perm (Fin 22) :=
  permOf 22 [[1,19,2],[3,4,10],[5,7,13],[6,16,14],[11,15,21],[12,18,20]]

@[expose] def g1 : Perm (Fin 22) :=
  permOf 22 [[0,9,1],[2,17,19],[3,10],[4,14,21,8,12,5],[6,13,15,11,16,20],[7,18]]

theorem l6Gens_eq : l6Gens = [g0, g1] := rfl

@[expose] def e1 : Perm (Fin 22) :=
  permOf 22 [[3, 10], [4, 8], [5, 21], [6, 11], [7, 18], [12, 14], [13, 16], [15, 20]]

@[expose] def e2 : Perm (Fin 22) :=
  permOf 22 [[3, 4], [5, 14], [6, 18], [7, 11], [8, 10], [12, 21], [13, 20], [15, 16]]

@[expose] def e3 : Perm (Fin 22) :=
  permOf 22 [[3, 5], [4, 14], [6, 13], [7, 15], [8, 12], [10, 21], [11, 16], [18, 20]]

@[expose] def e4 : Perm (Fin 22) :=
  permOf 22 [[3, 16], [4, 15], [5, 11], [6, 21], [7, 14], [8, 20], [10, 13], [12, 18]]

@[expose] def eL : List (Perm (Fin 22)) := [e1, e2, e3, e4]

@[expose] def spanOf : List (Perm (Fin 22)) → List (Perm (Fin 22))
  | [] => [1]
  | g :: gs => spanOf gs ++ (spanOf gs).map (g * ·)

@[expose] def hexL : List (Fin 22) := [0, 1, 2, 9, 17, 19]

theorem g0_eq : ∀ x : Fin 22, g0 x = evalW mGens
    [0, 1, 0, 1, 1, 0, 1, 1, 1, 0, 1, 1, 1, 0, 1, 1, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1] x := by
  decide +kernel

theorem g1_eq : ∀ x : Fin 22, g1 x = evalW mGens
    [1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1,
      1] x := by
  decide +kernel

theorem e1_eq : ∀ x : Fin 22, e1 x = evalW l6Gens [1, 1, 1] x := by
  decide +kernel

theorem e2_eq : ∀ x : Fin 22, e2 x = evalW l6Gens [0, 1, 1, 1, 0, 0] x := by
  decide +kernel

theorem e3_eq : ∀ x : Fin 22, e3 x = evalW l6Gens [1, 1, 0, 1, 1, 1, 0, 0, 1] x := by
  decide +kernel

theorem e4_eq : ∀ x : Fin 22, e4 x = evalW l6Gens [1, 0, 1, 0, 1, 1, 1, 1, 0, 1, 0] x := by
  decide +kernel

theorem c12 : ∀ x : Fin 22, e1 (e2 x) = e2 (e1 x) := by decide +kernel
theorem c13 : ∀ x : Fin 22, e1 (e3 x) = e3 (e1 x) := by decide +kernel
theorem c14 : ∀ x : Fin 22, e1 (e4 x) = e4 (e1 x) := by decide +kernel
theorem c23 : ∀ x : Fin 22, e2 (e3 x) = e3 (e2 x) := by decide +kernel
theorem c24 : ∀ x : Fin 22, e2 (e4 x) = e4 (e2 x) := by decide +kernel
theorem c34 : ∀ x : Fin 22, e3 (e4 x) = e4 (e3 x) := by decide +kernel

theorem f1 : ∀ x ∈ hexL, e1 x = x := by decide +kernel

theorem orbit3 : ∀ x : Fin 22, x ∉ hexL → ∃ s ∈ spanOf eL, s 3 = x := by
  decide +kernel

theorem e1_three : e1 3 = 10 := by decide +kernel

theorem card_compl_hexL : (Finset.univ.filter fun x : Fin 22 => x ∉ hexL).card = 16 := by
  decide +kernel

theorem n01 : ∀ x : Fin 22, g0 (e1 (g0⁻¹ x)) = e2 x := by decide +kernel
theorem n02 : ∀ x : Fin 22, g0 (e2 (g0⁻¹ x)) = (e1 * e2) x := by decide +kernel
theorem n03 : ∀ x : Fin 22, g0 (e3 (g0⁻¹ x)) = (e3 * e4) x := by decide +kernel
theorem n04 : ∀ x : Fin 22, g0 (e4 (g0⁻¹ x)) = e3 x := by decide +kernel
theorem n11 : ∀ x : Fin 22, g1 (e1 (g1⁻¹ x)) = e1 x := by decide +kernel
theorem n12 : ∀ x : Fin 22, g1 (e2 (g1⁻¹ x)) = (e1 * e2 * e3) x := by decide +kernel
theorem n13 : ∀ x : Fin 22, g1 (e3 (g1⁻¹ x)) = (e1 * e2) x := by decide +kernel
theorem n14 : ∀ x : Fin 22, g1 (e4 (g1⁻¹ x)) = (e2 * e4) x := by decide +kernel
theorem m01 : ∀ x : Fin 22, g0⁻¹ (e1 (g0 x)) = (e1 * e2) x := by decide +kernel
theorem m02 : ∀ x : Fin 22, g0⁻¹ (e2 (g0 x)) = e1 x := by decide +kernel
theorem m03 : ∀ x : Fin 22, g0⁻¹ (e3 (g0 x)) = e4 x := by decide +kernel
theorem m04 : ∀ x : Fin 22, g0⁻¹ (e4 (g0 x)) = (e3 * e4) x := by decide +kernel
theorem m11 : ∀ x : Fin 22, g1⁻¹ (e1 (g1 x)) = e1 x := by decide +kernel
theorem m12 : ∀ x : Fin 22, g1⁻¹ (e2 (g1 x)) = (e1 * e3) x := by decide +kernel
theorem m13 : ∀ x : Fin 22, g1⁻¹ (e3 (g1 x)) = (e2 * e3) x := by decide +kernel
theorem m14 : ∀ x : Fin 22, g1⁻¹ (e4 (g1 x)) = (e1 * e3 * e4) x := by decide +kernel

theorem base_out : ∀ x : Fin 22, x.val < 5 → m22gA⁻¹ x ∉ hexL := by
  decide +kernel

theorem fix_outRep1 : (Finset.univ.filter fun x : Fin 22 => m22OutRep1 x = x).card < 16 := by
  decide +kernel

theorem fix_outRep2 : (Finset.univ.filter fun x : Fin 22 => m22OutRep2 x = x).card < 16 := by
  decide +kernel

end CFSG.Quasithin.H13.S126M22
