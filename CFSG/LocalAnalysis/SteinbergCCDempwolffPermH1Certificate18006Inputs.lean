module

public import CFSG.LocalAnalysis.SteinbergCCDempwolffBasic

public section

namespace CFSG.LocalAnalysis.DempwolffFive

open Matrix

abbrev PF := Fin 31 → ZMod 2

@[expose] def pMat : Matrix (Fin 5) (Fin 5) (ZMod 2) :=
  fun i j => if i.1 = (j.1 + 1) % 5 then 1 else 0

theorem pMat_mul_transpose : pMat * pMatᵀ = 1 := by decide

theorem pMat_transpose_mul : pMatᵀ * pMat = 1 := by decide

@[expose] def gpc : G := ⟨pMat, pMatᵀ, pMat_mul_transpose, pMat_transpose_mul⟩

@[expose] def ga : G := xg (0, 1, 1)

@[expose] def genArr0 : Array (Fin 31) := permArr ga

@[expose] def genArr1 : Array (Fin 31) := permArr ga⁻¹

@[expose] def genArr2 : Array (Fin 31) := permArr gpc

@[expose] def genArr3 : Array (Fin 31) := permArr gpc⁻¹

@[expose] def genArr (l : ℕ) : Array (Fin 31) :=
  if l = 0 then genArr0 else if l = 1 then genArr1 else if l = 2 then genArr2 else genArr3

@[expose] def evalArr (w : List ℕ) : Array (Fin 31) :=
  w.foldr (fun l acc => compA (genArr l) acc) (permArr 1)

end CFSG.LocalAnalysis.DempwolffFive
