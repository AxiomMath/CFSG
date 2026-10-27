module

public import CFSG.RankThree.PartOne.K159.AutPairFive
public import CFSG.RankThree.PartOne.K159.AutA10

public section

namespace CFSG.RankThree.PartOne.K159

theorem gP_moves_six : ∀ k : ℕ, 1 ≤ k → k ≤ 6 → gP ^ k * aP * (gP ^ k)⁻¹ ≠ aP := by
  intro k hk1 hk6
  interval_cases k <;> decide

theorem pair_inj_ten : ∀ i j i' j' : ℕ, i < 5 → j < 5 → i' < 5 → j' < 5 →
    aP ^ i * bP ^ j = aP ^ i' * bP ^ j' → i = i' ∧ j = j' := by
  intro i j i' j' hi hj hi' hj' h
  have h1 := pairP_zero_five ⟨i, hi⟩ ⟨j, hj⟩
  have h2 := pairP_zero_five ⟨i', hi'⟩ ⟨j', hj'⟩
  have h' : pairP i j = pairP i' j' := h
  have e0 := congrArg (fun σ : Equiv.Perm (Fin 10) => σ 0) h'
  have e5 := congrArg (fun σ : Equiv.Perm (Fin 10) => σ 5) h'
  simp only [h1.1, h2.1, Fin.mk.injEq] at e0
  simp only [h1.2, h2.2, Fin.mk.injEq] at e5
  exact ⟨e0, by omega⟩

theorem autWitnessUpTo_six_alternating_ten : AutWitnessUpTo 6 5 (alternatingGroup (Fin 10)) :=
  autWitnessUpTo_of_pair Nat.prime_five (alternatingGroup (Fin 10)) (a := aP) (b := bP) (g := gP)
    ((Equiv.Perm.mem_alternatingGroup).2 sign_aP) ((Equiv.Perm.mem_alternatingGroup).2 sign_bP)
    gP_mem_alternating aP_pow bP_pow aP_comm_bP pair_inj_ten
    ⟨0, 2, by simpa using gP_aP⟩ ⟨1, 0, by simpa using gP_bP⟩ gP_moves_six

end CFSG.RankThree.PartOne.K159
