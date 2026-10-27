module

public import CFSG.Quasithin.Recognition.J2RecEndgame

public section

namespace CFSG.Quasithin

open CFSG.Sporadic.Bridge.J2 (lwordL idL toM)
open CFSG.Timmesfeld.Moufang.J2 (genL)

@[expose] def j2W5 : List ℕ := [1, 2, 3, 1, 4, 2, 1, 3, 6, 1]

@[expose] def j2W3 : List ℕ := [1, 0, 1, 2, 3, 1, 0, 2, 1, 0, 3, 1, 4]

@[expose] def j2G (j : ℕ) : List ℕ := [1, 0, j + 2, 1, 0, 1]

theorem j2W5_comm : lwordL genL genL (posWord (j2W5 ++ [0])) idL =
    lwordL genL genL (posWord ([0] ++ j2W5)) idL := by decide +kernel

theorem j2W5_pow : lwordL genL genL (posWord (j2W5 ++ j2W5 ++ j2W5 ++ j2W5 ++ j2W5)) idL =
    lwordL genL genL (posWord []) idL := by decide +kernel

theorem j2W5_ne : toM (lwordL genL genL (posWord j2W5) idL) ≠ 1 := by decide +kernel

theorem j2W3_comm : lwordL genL genL (posWord (j2W3 ++ [0])) idL =
    lwordL genL genL (posWord ([0] ++ j2W3)) idL := by decide +kernel

theorem j2W3_pow : lwordL genL genL (posWord (j2W3 ++ j2W3 ++ j2W3)) idL =
    lwordL genL genL (posWord []) idL := by decide +kernel

theorem j2W3_ne : toM (lwordL genL genL (posWord j2W3) idL) ≠ 1 := by decide +kernel

theorem j2G_conj_d : ∀ j : Fin 5, lwordL genL genL (posWord (j2G j.val ++ [0])) idL =
    lwordL genL genL (posWord ([j.val + 2] ++ j2G j.val)) idL := by decide +kernel

theorem j2G_conj_x : ∀ j : Fin 5, lwordL genL genL (posWord (j2G j.val ++ [j.val + 2])) idL =
    lwordL genL genL (posWord ([0, j.val + 2] ++ j2G j.val)) idL := by decide +kernel

namespace J2LineEndgame

variable {H : Type} [Group H] {d c : H} {x : Fin 5 → H}

theorem exists_words (hE : J2LineEndgame) (h1 : J2FiveLines d x) (h2 : J2ClosingRels d c x) :
    ∃ (w₃ w₅ : H) (g : Fin 5 → H),
      w₃ ∈ Subgroup.closure (insert d (insert c (Set.range x))) ∧
      w₅ ∈ Subgroup.closure (insert d (insert c (Set.range x))) ∧
      (∀ j, g j ∈ Subgroup.closure (insert d (insert c (Set.range x)))) ∧
      w₃ * d = d * w₃ ∧ w₃ ^ 3 = 1 ∧ w₃ ≠ 1 ∧
      w₅ * d = d * w₅ ∧ w₅ ^ 5 = 1 ∧ w₅ ≠ 1 ∧
      ∀ j, g j * d = x j * g j ∧ g j * x j = d * x j * g j := by
  set K := Subgroup.closure (insert d (insert c (Set.range x))) with hK
  set g7 := lineGen7 d c x with hg7
  have hmem : ∀ w : List ℕ, (w.map g7).prod ∈ K := fun w =>
    Subgroup.list_prod_mem K fun y hy => by
      obtain ⟨i, -, rfl⟩ := List.mem_map.mp hy
      exact lineGen7_mem_closure d c x i
  refine ⟨(j2W3.map g7).prod, (j2W5.map g7).prod, fun j => ((j2G j.val).map g7).prod,
    hmem _, hmem _, fun j => hmem _, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have := eval_eq hE h1 h2 (u := j2W3 ++ [0]) (v := [0] ++ j2W3) j2W3_comm
    simpa [List.map_append, lineGen7_zero, hg7] using this
  · have := eval_eq hE h1 h2 (u := j2W3 ++ j2W3 ++ j2W3) (v := []) j2W3_pow
    simpa [List.map_append, pow_succ, mul_assoc] using this
  · intro h
    exact eval_ne_one hE h1 h2 j2W3_ne h
  · have := eval_eq hE h1 h2 (u := j2W5 ++ [0]) (v := [0] ++ j2W5) j2W5_comm
    simpa [List.map_append, lineGen7_zero, hg7] using this
  · have := eval_eq hE h1 h2 (u := j2W5 ++ j2W5 ++ j2W5 ++ j2W5 ++ j2W5) (v := []) j2W5_pow
    simpa [List.map_append, pow_succ, mul_assoc] using this
  · intro h
    exact eval_ne_one hE h1 h2 j2W5_ne h
  · intro j
    constructor
    · have := eval_eq hE h1 h2 (u := j2G j.val ++ [0]) (v := [j.val + 2] ++ j2G j.val)
        (j2G_conj_d j)
      simpa [List.map_append, lineGen7_zero, lineGen7_two_add, hg7] using this
    · have := eval_eq hE h1 h2 (u := j2G j.val ++ [j.val + 2]) (v := [0, j.val + 2] ++ j2G j.val)
        (j2G_conj_x j)
      simpa [List.map_append, lineGen7_zero, lineGen7_two_add, hg7, mul_assoc] using this

end J2LineEndgame

end CFSG.Quasithin
