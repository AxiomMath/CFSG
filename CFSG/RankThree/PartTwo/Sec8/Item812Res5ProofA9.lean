module

public import CFSG.RankThree.PartTwo.Sec4.T444.Item434AltPerm
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434KitWreath

public section

namespace CFSG.RankThree.PartTwo.Sec8.Item812Res5

open Equiv Equiv.Perm Subgroup CFSG.RankThree.PartTwo.Sec4.Item434Kit
  CFSG.RankThree.PartTwo.Sec4.Item434AltPerm

@[expose] def zPerm9 : Fin 3 → Perm (Fin 9) :=
  ![c1 9, c2 9, c3 9]

theorem vecElt_zPerm9 (v : Fin 3 → ZMod 3) : vecElt zPerm9 v = vecPerm 9 v :=
  rfl

theorem wreathFacts_perm9 : WreathFacts zPerm9 (tt 9) where
  pow_z := by
    intro i
    fin_cases i <;> decide
  comm_z := by
    intro i j
    fin_cases i <;> fin_cases j <;> decide
  inj := fun v hv => wFacts_nine.inj v hv
  pow_t := wFacts_nine.tt_pow
  conj0 := wFacts_nine.conj1
  conj1 := wFacts_nine.conj2
  conj2 := wFacts_nine.conj3
  t_ne := wFacts_nine.tt_ne

theorem zPerm9_mem (i : Fin 3) : zPerm9 i ∈ alternatingGroup (Fin 9) := by
  fin_cases i
  · change c1 9 ∈ alternatingGroup (Fin 9)
    rw [mem_alternatingGroup, c1, Perm.sign_mul, sign_swap (by decide), sign_swap (by decide)]
    decide
  · change c2 9 ∈ alternatingGroup (Fin 9)
    rw [mem_alternatingGroup, c2, Perm.sign_mul, sign_swap (by decide), sign_swap (by decide)]
    decide
  · change c3 9 ∈ alternatingGroup (Fin 9)
    rw [mem_alternatingGroup, c3, Perm.sign_mul, sign_swap (by decide), sign_swap (by decide)]
    decide

theorem tt_nine_mem : tt 9 ∈ alternatingGroup (Fin 9) := by
  rw [mem_alternatingGroup, tt]
  simp only [Perm.sign_mul, sign_swap (show (0 : Fin 9) ≠ 3 by decide),
    sign_swap (show (3 : Fin 9) ≠ 6 by decide), sign_swap (show (1 : Fin 9) ≠ 4 by decide),
    sign_swap (show (4 : Fin 9) ≠ 7 by decide), sign_swap (show (2 : Fin 9) ≠ 5 by decide),
    sign_swap (show (5 : Fin 9) ≠ 8 by decide)]
  decide

@[expose] def zA9 : Fin 3 → alternatingGroup (Fin 9) :=
  fun i => ⟨zPerm9 i, zPerm9_mem i⟩

@[expose] def tA9 : alternatingGroup (Fin 9) :=
  ⟨tt 9, tt_nine_mem⟩

theorem wreathFacts_A9 : WreathFacts zA9 tA9 :=
  wreathFacts_perm9.subtype zPerm9_mem tt_nine_mem

theorem factorization_card_A9 : (Nat.card (alternatingGroup (Fin 9))).factorization 3 = 4 := by
  rw [Nat.card_eq_fintype_card, card_alternatingGroup, Fintype.card_fin,
    show (Nat.factorial 9) / 2 = 3 ^ 4 * 2240 by decide,
    factorization_three_pow_mul 4 (by norm_num)]

theorem card_wreathW_A9 : Nat.card (wreathW zA9 tA9) = 81 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hle := card_le_of_isPGroup (isPGroup_wreathW wreathFacts_A9)
  rw [factorization_card_A9] at hle
  have := le_card_wreathW wreathFacts_A9
  norm_num at hle
  omega

theorem card_wreathW_A9_eq_pow :
    Nat.card (wreathW zA9 tA9) = 3 ^ (Nat.card (alternatingGroup (Fin 9))).factorization 3 := by
  rw [card_wreathW_A9, factorization_card_A9]
  norm_num

@[expose] def kPerm9 : Perm (Fin 9) :=
  swap 0 3 * swap 3 4 * swap 4 1 * (swap 2 6 * swap 6 5 * swap 5 7)

theorem kPerm9_mem : kPerm9 ∈ alternatingGroup (Fin 9) := by
  rw [mem_alternatingGroup, kPerm9]
  simp only [Perm.sign_mul, sign_swap (show (0 : Fin 9) ≠ 3 by decide),
    sign_swap (show (3 : Fin 9) ≠ 4 by decide), sign_swap (show (4 : Fin 9) ≠ 1 by decide),
    sign_swap (show (2 : Fin 9) ≠ 6 by decide), sign_swap (show (6 : Fin 9) ≠ 5 by decide),
    sign_swap (show (5 : Fin 9) ≠ 7 by decide)]
  decide

@[expose] def kA9 : alternatingGroup (Fin 9) :=
  ⟨kPerm9, kPerm9_mem⟩

theorem kPerm9_conj : kPerm9 * tt 9 * kPerm9⁻¹ = vecPerm 9 ![1, 1, 1] := by
  decide

theorem kA9_conj_mem_baseA : kA9 * tA9 * kA9⁻¹ ∈ baseA zA9 := by
  have h : kA9 * tA9 * kA9⁻¹ = vecElt zA9 ![1, 1, 1] := by
    apply Subtype.ext
    change kPerm9 * tt 9 * kPerm9⁻¹ = _
    rw [kPerm9_conj]
    simp [vecElt, zA9, zPerm9, vecPerm]
  rw [h]
  exact vecElt_mem_baseA wreathFacts_A9 _

end CFSG.RankThree.PartTwo.Sec8.Item812Res5
