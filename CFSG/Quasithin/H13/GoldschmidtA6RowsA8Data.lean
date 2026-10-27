module

public import CFSG.Quasithin.H13.GoldschmidtA6RowsA8Q

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

open Equiv Matrix

namespace CFSG.Quasithin.H13.A6.GR

namespace Row8

@[expose] def g1 : Perm (Fin 8) :=
  swap 0 7 * swap 7 1 * swap 1 6 * (swap 2 4 * swap 4 3 * swap 3 5)

@[expose] def g2 : Perm (Fin 8) := swap 0 1 * (swap 4 6 * swap 6 5 * swap 5 7)

@[expose] def g3 : Perm (Fin 8) :=
  swap 0 5 * swap 5 3 * swap 3 7 * (swap 1 4 * swap 4 2 * swap 2 6)

theorem g1_mem : g1 ∈ alternatingGroup (Fin 8) := by
  rw [Equiv.Perm.mem_alternatingGroup, g1]
  decide

theorem g2_mem : g2 ∈ alternatingGroup (Fin 8) := by
  rw [Equiv.Perm.mem_alternatingGroup, g2]
  decide

theorem g3_mem : g3 ∈ alternatingGroup (Fin 8) := by
  rw [Equiv.Perm.mem_alternatingGroup, g3]
  decide

@[expose] def x1 : ↥(alternatingGroup (Fin 8)) := ⟨g1, g1_mem⟩

@[expose] def x2 : ↥(alternatingGroup (Fin 8)) := ⟨g2, g2_mem⟩

@[expose] def x3 : ↥(alternatingGroup (Fin 8)) := ⟨g3, g3_mem⟩

theorem mat_g1 : mat8 g1 = matOfCols 6 [9, 2, 32, 8, 27, 6] := by decide +kernel

theorem mat_g1inv : mat8 g1⁻¹ = matOfCols 6 [9, 2, 34, 8, 19, 4] := by decide +kernel

theorem mat_g2 : mat8 g2 = matOfCols 6 [1, 2, 5, 10, 59, 41] := by decide +kernel

theorem mat_g2inv : mat8 g2⁻¹ = matOfCols 6 [1, 2, 5, 10, 50, 43] := by decide +kernel

theorem mat_g3 : mat8 g3 = matOfCols 6 [11, 2, 34, 10, 49, 4] := by decide +kernel

theorem mat_g3inv : mat8 g3⁻¹ = matOfCols 6 [9, 2, 32, 10, 31, 6] := by decide +kernel

@[expose] def gcs8 : List (↥(alternatingGroup (Fin 8)) × List ℕ) :=
  [(x1, [9, 2, 32, 8, 27, 6]), (x1⁻¹, [9, 2, 34, 8, 19, 4]),
    (x2, [1, 2, 5, 10, 59, 41]), (x2⁻¹, [1, 2, 5, 10, 50, 43]),
    (x3, [11, 2, 34, 10, 49, 4]), (x3⁻¹, [9, 2, 32, 10, 31, 6])]

@[expose] def gcols8 : List (List ℕ) :=
  [[9, 2, 32, 8, 27, 6], [9, 2, 34, 8, 19, 4],
    [1, 2, 5, 10, 59, 41], [1, 2, 5, 10, 50, 43],
    [11, 2, 34, 10, 49, 4], [9, 2, 32, 10, 31, 6]]

theorem gcols8_eq : gcs8.map Prod.snd = gcols8 := rfl


@[expose] def gm8 : List (List ℕ) :=
  [[9, 2, 32, 8, 27, 6], [1, 2, 5, 10, 59, 41], [11, 2, 34, 10, 49, 4]]

@[expose] def gp8 : List (List ℕ × List ℕ) :=
  [([9, 2, 32, 8, 27, 6], [9, 2, 34, 8, 19, 4]),
    ([1, 2, 5, 10, 59, 41], [1, 2, 5, 10, 50, 43]),
    ([11, 2, 34, 10, 49, 4], [9, 2, 32, 10, 31, 6])]

@[expose] def u8 : ℕ := 16

@[expose] def words8 : List (List ℕ) := [[], [0], [1], [2], [0, 0], [0, 1]]

@[expose] def binv8 : List ℕ := [15, 29, 45, 17, 1, 6]

theorem hB8c : isOne 6 (mulC 6 (ccolsC 6 gm8 words8 u8) binv8) = true := by decide +kernel

theorem hw8 : words8.length = 6 := by decide

theorem gp8_len : ∀ p ∈ gp8, p.1.length = 6 ∧ p.2.length = 6 := by decide

theorem cond8 : ∀ w < 2 ^ 6, condC 6 gm8 words8 binv8 w = true → w = 24 ∨ w = 26 := by
  decide +kernel

theorem hs24 : ∀ cs ∈ bt 6 (fun pre c => okQ8 pre c &&
    commOk1 6 (pcolsC 6 gm8 words8 binv8 24) (pre ++ [c])) 6,
      leafF gp8 fullQ8 7 cs = true := by
  decide +kernel

theorem hs26 : ∀ cs ∈ bt 6 (fun pre c => okQ8 pre c &&
    commOk1 6 (pcolsC 6 gm8 words8 binv8 26) (pre ++ [c])) 6,
      leafF gp8 fullQ8 7 cs = true := by
  decide +kernel

theorem hsearch8 : ∀ w < 2 ^ 6, condC 6 gm8 words8 binv8 w = true →
    ∀ cs ∈ bt 6 (fun pre c => okQ8 pre c &&
      commOk 6 (pcolsC 6 gm8 words8 binv8 w) (pre ++ [c])) 6,
        leafC 6 gp8 fullQ8 7 cs = true := by
  intro w hw hc cs hcs
  have hlen := length_of_mem_bt 6 6 cs hcs
  have hcs' : ∀ w', cs ∈ bt 6 (fun pre c => okQ8 pre c &&
      commOk 6 (pcolsC 6 gm8 words8 binv8 w') (pre ++ [c])) 6 →
      cs ∈ bt 6 (fun pre c => okQ8 pre c &&
        commOk1 6 (pcolsC 6 gm8 words8 binv8 w') (pre ++ [c])) 6 := fun w' h =>
    bt_mono 6 (fun pre c h => by
      rw [Bool.and_eq_true] at h ⊢
      exact ⟨h.1, commOk1_of_commOk h.2⟩) 6 cs h
  rcases cond8 w hw hc with rfl | rfl
  · exact leafF_imp gp8_len hlen (hs24 cs (hcs' _ hcs))
  · exact leafF_imp gp8_len hlen (hs26 cs (hcs' _ hcs))


@[expose] def slist8 : List (List ℕ) :=
  [
    [1, 2, 4, 8, 16, 32], [9, 2, 32, 8, 27, 6], [1, 2, 5, 10, 59, 41], [11, 2, 34, 10, 49, 4],
    [9, 2, 34, 8, 19, 4], [1, 2, 5, 10, 50, 43], [9, 2, 32, 10, 31, 6], [1, 2, 6, 8, 24, 34],
    [11, 2, 41, 10, 50, 7], [1, 2, 4, 10, 50, 32], [11, 2, 43, 10, 59, 7], [3, 2, 6, 10, 30, 34],
    [9, 2, 41, 10, 30, 7], [1, 2, 4, 8, 27, 34], [11, 2, 41, 8, 54, 5], [9, 2, 43, 10, 20, 5],
    [9, 2, 41, 8, 24, 5], [3, 2, 4, 10, 20, 32], [9, 2, 43, 8, 19, 5], [3, 2, 6, 8, 62, 34],
    [11, 2, 43, 10, 56, 5], [1, 2, 6, 10, 56, 34], [11, 2, 41, 10, 49, 5], [9, 2, 41, 10, 31, 5],
    [11, 2, 41, 8, 55, 7], [9, 2, 43, 10, 21, 7], [9, 2, 41, 8, 27, 7], [11, 2, 43, 8, 62, 7],
    [1, 2, 7, 10, 49, 43], [11, 2, 32, 10, 59, 6], [1, 2, 7, 10, 56, 41], [9, 2, 34, 10, 21, 4],
    [3, 2, 7, 10, 31, 43], [9, 2, 34, 8, 16, 6], [3, 2, 5, 8, 55, 43], [3, 2, 5, 10, 21, 41],
    [1, 2, 5, 8, 27, 43], [1, 2, 5, 8, 16, 41], [11, 2, 34, 8, 55, 4], [3, 2, 5, 10, 30, 43],
    [3, 2, 7, 8, 54, 43], [3, 2, 7, 10, 20, 41], [1, 2, 7, 8, 24, 43], [3, 2, 7, 8, 63, 41],
    [11, 2, 34, 8, 54, 6], [11, 2, 32, 8, 63, 6], [9, 2, 32, 8, 24, 4], [11, 2, 34, 10, 50, 6],
    [9, 2, 32, 10, 30, 4], [11, 2, 32, 8, 62, 4], [1, 2, 7, 8, 19, 41], [11, 2, 32, 10, 56, 4],
    [3, 2, 5, 8, 62, 41], [9, 2, 34, 10, 20, 6], [1, 2, 6, 8, 19, 32], [9, 2, 43, 8, 16, 7],
    [3, 2, 4, 8, 54, 32], [11, 2, 43, 8, 63, 5], [3, 2, 6, 8, 55, 32], [1, 2, 6, 10, 49, 32],
    [3, 2, 4, 10, 31, 34], [3, 2, 4, 8, 63, 34], [1, 2, 4, 10, 59, 34], [3, 2, 6, 10, 21, 32]]

theorem slist8_len : slist8.all (fun c => c.length == 6) = true := by decide +kernel

theorem slist8_one : ∃ c ∈ slist8, normC 6 c = normC 6 (oneC 6) := by decide +kernel

theorem slist8_cl_fast : slist8.all (fun c => gcols8.all fun p =>
    slist8.any fun c' => c' == mulL p c) = true := by decide +kernel

theorem slist8_pow_fast : slist8.all (fun c => isOneL (sqIterL c 3)) = true := by decide +kernel

end Row8

end CFSG.Quasithin.H13.A6.GR
