module

public import CFSG.Quasithin.Vol2.Ch10SecQ9H2

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecC.C10P4F

open Matrix CFSG.QuasithinUnique

@[expose] def par5 (v : Fin 10 → ZMod 2) : Matrix (Fin 5) (Fin 5) (ZMod 2) :=
  !![1, v 0, v 1, v 2, v 3; 0, 1, v 4, v 5, v 6; 0, 0, 1, v 7, v 8; 0, 0, 0, 1, v 9;
    0, 0, 0, 0, 1]

theorem isUniTri_par5 (v : Fin 10 → ZMod 2) : IsUniTri (par5 v) := by
  refine ⟨fun i j h => ?_, fun i => ?_⟩
  · fin_cases i <;> fin_cases j <;> simp_all [par5]
  · fin_cases i <;> simp [par5]

theorem det_par5 (v : Fin 10 → ZMod 2) : (par5 v).det = 1 := by
  rw [det_of_isUpperTriangular (isUniTri_par5 v).1]
  exact Finset.prod_eq_one fun i _ => (isUniTri_par5 v).2 i

@[expose] def par5SL (v : Fin 10 → ZMod 2) : ↥(uniSL 5) :=
  ⟨⟨par5 v, det_par5 v⟩, isUniTri_par5 v⟩

theorem par5_injective : Function.Injective par5 := by
  intro v w h
  funext k
  fin_cases k
  · exact congrFun (congrFun h 0) 1
  · exact congrFun (congrFun h 0) 2
  · exact congrFun (congrFun h 0) 3
  · exact congrFun (congrFun h 0) 4
  · exact congrFun (congrFun h 1) 2
  · exact congrFun (congrFun h 1) 3
  · exact congrFun (congrFun h 1) 4
  · exact congrFun (congrFun h 2) 3
  · exact congrFun (congrFun h 2) 4
  · exact congrFun (congrFun h 3) 4

theorem exists_par5 {M : Matrix (Fin 5) (Fin 5) (ZMod 2)} (hM : IsUniTri M) :
    M = par5 ![M 0 1, M 0 2, M 0 3, M 0 4, M 1 2, M 1 3, M 1 4, M 2 3, M 2 4, M 3 4] := by
  obtain ⟨hT, hD⟩ := hM
  have h10 : M 1 0 = 0 := hT (by decide)
  have h20 : M 2 0 = 0 := hT (by decide)
  have h21 : M 2 1 = 0 := hT (by decide)
  have h30 : M 3 0 = 0 := hT (by decide)
  have h31 : M 3 1 = 0 := hT (by decide)
  have h32 : M 3 2 = 0 := hT (by decide)
  have h40 : M 4 0 = 0 := hT (by decide)
  have h41 : M 4 1 = 0 := hT (by decide)
  have h42 : M 4 2 = 0 := hT (by decide)
  have h43 : M 4 3 = 0 := hT (by decide)
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [par5, hD, h10, h20, h21, h30, h31, h32, h40, h41, h42, h43]

theorem par5SL_bijective : Function.Bijective par5SL := by
  constructor
  · intro v w h
    exact par5_injective (congrArg (fun A : ↥(uniSL 5) =>
      ((A : Matrix.SpecialLinearGroup (Fin 5) (ZMod 2)) : Matrix (Fin 5) (Fin 5) (ZMod 2))) h)
  · intro A
    set M := ((A : Matrix.SpecialLinearGroup (Fin 5) (ZMod 2)) : Matrix (Fin 5) (Fin 5) (ZMod 2))
      with hM
    refine ⟨![M 0 1, M 0 2, M 0 3, M 0 4, M 1 2, M 1 3, M 1 4, M 2 3, M 2 4, M 3 4],
      Subtype.ext (Matrix.SpecialLinearGroup.ext _ _ fun i j => ?_)⟩
    exact (congrFun (congrFun (exists_par5 A.2) i) j).symm

theorem card_uniSL_five : Nat.card (uniSL 5) = 1024 := by
  rw [← Nat.card_congr (Equiv.ofBijective _ par5SL_bijective), Nat.card_eq_fintype_card]
  simp

theorem isPGroup_uniSL_five : IsPGroup 2 (uniSL 5) :=
  IsPGroup.of_card (n := 10) (by rw [card_uniSL_five]; norm_num)

end CFSG.Quasithin.Vol2.Ch10.SecC.C10P4F
