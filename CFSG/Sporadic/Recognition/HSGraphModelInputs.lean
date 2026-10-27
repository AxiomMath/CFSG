module

public import CFSG.LocalAnalysis.ComponentClassification.WittDesignM22HexadsBase
public import CFSG.Sporadic.Recognition.HSGraphDefs

public section

namespace CFSG.Sporadic.Recognition.HSGraph

open CFSG.ComponentClassification.WittDesign

theorem getD_mem_hexads (i : ℕ) : hexadList.getD i hexad0 ∈ hexads := by
  rw [mem_hexads]
  by_cases h : i < hexadList.length
  · rw [List.getD_eq_getElem _ _ h]
    exact List.getElem_mem h
  · rw [List.getD_eq_default _ _ (not_lt.1 h)]
    exact List.mem_cons_self

@[expose] def modelBlkAt (i : ℕ) : {B // B ∈ hexads} :=
  ⟨hexadList.getD i hexad0, getD_mem_hexads i⟩

@[expose] def modelVertAt (n : ℕ) : Vert hexads :=
  if n = 0 then vInf else if n ≤ 22 then vPt ⟨(n - 1) % 22, Nat.mod_lt _ (by norm_num)⟩
    else vBlk (modelBlkAt (n - 23))

@[expose] def modelVertAtF (i : Fin 100) : Vert hexads := modelVertAt i

@[expose] def psiList : List ℕ := [
  1, 23, 25, 24, 33, 41, 29, 39, 43, 36,
  26, 40, 32, 30, 42, 28, 34, 37, 0, 38,
  27, 35, 31, 2, 98, 76, 77, 97, 84, 89,
  90, 85, 10, 94, 83, 73, 81, 75, 3, 18,
  72, 80, 88, 20, 95, 99, 71, 69, 67, 68,
  6, 19, 62, 79, 5, 92, 61, 14, 93, 78,
  64, 70, 4, 21, 63, 91, 96, 82, 7, 66,
  15, 86, 57, 51, 12, 56, 45, 59, 17, 87,
  47, 55, 74, 44, 48, 46, 9, 13, 49, 53,
  50, 22, 8, 65, 52, 16, 60, 58, 54, 11]

@[expose] def psiFun (i : Fin 100) : Fin 100 :=
  ⟨(psiList.getD i 0) % 100, Nat.mod_lt _ (by norm_num)⟩

@[expose] def psiInvFun (i : Fin 100) : Fin 100 :=
  ((List.finRange 100).find? fun j => psiFun j == i).getD 0

end CFSG.Sporadic.Recognition.HSGraph
