module

public import CFSG.Monster.Schur.M24
public import CFSG.Sporadic.Co1.Cover.FoxProof

public section

namespace CFSG.Sporadic.Co1.Cover

open CFSG.Monster.Schur.M24 CFSG.Sporadic.SmallF2

theorem gen_sq :
    gen 0 * gen 0 = 1 := by
  have h := lift_gen_eq_one a2_mem
  simpa [a2, FreeGroup.lift_mk] using h

theorem gen_cube :
    gen 1 * (gen 1 * gen 1) = 1 := by
  have h := gen_pow_three
  simpa [pow_succ, mul_assoc] using h

theorem eltPos_posWord
    (w : List (Fin 2 × Bool)) :
    eltPos (gen 0) (gen 1) (posWord w) =
      (w.map fun x => cond x.2 (gen x.1) (gen x.1)⁻¹).prod := by
  induction w with
  | nil => simp [posWord, eltPos]
  | cons l w ih =>
    obtain ⟨i, s⟩ := l
    have e : eltPos (gen 0) (gen 1) (posWord ((i, s) :: w)) =
        eltPos (gen 0) (gen 1) (if i = 0 then [false] else if s then [true] else [true, true]) *
          eltPos (gen 0) (gen 1) (posWord w) := by
      simp only [posWord, List.flatMap_cons, eltPos, List.map_append, List.prod_append]
    rw [e, ih, List.map_cons, List.prod_cons]
    congr 1
    fin_cases i
    · cases s
      · simp [eltPos, inv_eq_of_mul_eq_one_right gen_sq]
      · simp [eltPos]
    · cases s
      · simp [eltPos, inv_eq_of_mul_eq_one_right gen_cube]
      · simp [eltPos]

theorem hrel_M24
    (i : Fin 6) : eltPos (gen 0) (gen 1) (wordsPos i) = 1 := by
  have key : ∀ w : List (Fin 2 × Bool), castTo w ∈ pres.relators →
      eltPos (gen 0) (gen 1) (posWord w) = 1 := by
    intro w hw
    rw [eltPos_posWord]
    have := lift_gen_eq_one hw
    rwa [FreeGroup.lift_mk] at this
  fin_cases i
  · exact key _ a2_mem
  · exact key _ b3_mem
  · exact key _ ab23_mem
  · exact key _ r5_mem
  · exact key _ r6_mem
  · exact key _ r7_mem

end CFSG.Sporadic.Co1.Cover
