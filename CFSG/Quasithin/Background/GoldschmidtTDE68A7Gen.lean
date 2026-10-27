module

public import CFSG.Quasithin.Background.GoldschmidtTDE68A7Five

public section

namespace CFSG.Quasithin.E6.Alt.A7

open Equiv Equiv.Perm CFSG.Quasithin.E6.Bar

@[expose] def c5 : Perm (Fin 7) :=
  mk7 ![1, 2, 3, 6, 4, 5, 0] ![6, 0, 1, 2, 4, 5, 3] (by decide) (by decide)

@[expose] def c3 : Perm (Fin 7) :=
  mk7 ![0, 1, 2, 3, 5, 6, 4] ![0, 1, 2, 3, 6, 4, 5] (by decide) (by decide)

theorem c5_even : c5 ∈ alternatingGroup (Fin 7) := by
  rw [mem_alternatingGroup]
  decide +kernel

theorem c3_even : c3 ∈ alternatingGroup (Fin 7) := by
  rw [mem_alternatingGroup]
  decide +kernel

theorem toT_c5 : toT c5 = [1, 2, 3, 6, 4, 5, 0] := by decide +kernel

theorem toT_c3 : toT c3 = [0, 1, 2, 3, 5, 6, 4] := by decide +kernel

theorem c5_mem_N7 : (⟨c5, c5_even⟩ : G7) ∈ N7 := ⟨by decide, by decide⟩

theorem pa_comm_c3 : pa * c3 = c3 * pa :=
  toT_injective (by rw [toT_mul, toT_mul, toT_pa, toT_c3]; decide +kernel)

theorem c53_pow : (c5 * c3) ^ 7 = 1 := by
  have h : ∀ x : Perm (Fin 7), x ^ 7 = x * (x * (x * (x * (x * (x * x))))) := fun x => by
    simp [pow_succ, mul_assoc]
  rw [h]
  refine toT_injective ?_
  simp only [toT_mul, toT_c5, toT_c3, toT_one]
  decide +kernel

theorem c53_ne_one : c5 * c3 ≠ 1 := fun h => by
  have := congrArg toT h
  rw [toT_mul, toT_c5, toT_c3, toT_one] at this
  exact absurd this (by decide +kernel)

theorem orderOf_c53 : orderOf (c5 * c3) = 7 := by
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  exact orderOf_eq_prime c53_pow c53_ne_one

theorem D7q_le_fixedSub_pa : D7q ≤ fixedSub (cj pa) := by
  intro g hg
  rw [mem_fixedSub_cj]
  exact pa_comm _ hg

theorem cj_pa_mem : cj pa ∈ InvSet D7q := by
  rw [invSet_eq]
  simp

theorem cj_pb_mem : cj pb ∈ InvSet D7q := by
  rw [invSet_eq]
  simp

theorem fixedSub_pa_le : fixedSub (cj pa) ≤ ⨆ β ∈ InvSet D7q, fixedSub β :=
  le_iSup₂_of_le (cj pa) cj_pa_mem le_rfl

theorem fixedSub_pb_le : fixedSub (cj pb) ≤ ⨆ β ∈ InvSet D7q, fixedSub β :=
  le_iSup₂_of_le (cj pb) cj_pb_mem le_rfl

theorem gen_seven : ⨆ β ∈ InvSet D7q, fixedSub β = ⊤ := by
  set M : Subgroup G7 := ⨆ β ∈ InvSet D7q, fixedSub β with hM
  have h8 : 8 ∣ Nat.card M := by
    rw [← card_D7q]
    exact Subgroup.card_dvd_of_le (D7q_le_fixedSub_pa.trans fixedSub_pa_le)
  have h60 : 60 ∣ Nat.card M := by
    rw [← card_N7]
    exact Subgroup.card_dvd_of_le (N7_le_fixedSub_pb.trans fixedSub_pb_le)
  have h7 : 7 ∣ Nat.card M := by
    let x5 : G7 := ⟨c5, c5_even⟩
    let x3 : G7 := ⟨c3, c3_even⟩
    have hx5 : x5 ∈ M := fixedSub_pb_le (N7_le_fixedSub_pb c5_mem_N7)
    have hx3 : x3 ∈ M := fixedSub_pa_le ((mem_fixedSub_cj pa x3).2 pa_comm_c3)
    have hmem : x5 * x3 ∈ M := M.mul_mem hx5 hx3
    have hord : orderOf (x5 * x3) = 7 := by
      rw [← Subgroup.orderOf_coe (x5 * x3)]
      exact orderOf_c53
    have h3 := Subgroup.orderOf_dvd_natCard M hmem
    rwa [hord] at h3
  have hdvd : Nat.card M ∣ 2520 := card_alt7 ▸ Subgroup.card_subgroup_dvd_card M
  have h840 : 840 ∣ Nat.card M := by omega
  by_contra hne
  have hsimple : IsSimpleGroup G7 := alternatingGroup.isSimpleGroup (by simp)
  have hcore : M.normalCore = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal M.normalCore with h | h
    · exact h
    · exact absurd (top_le_iff.mp (h ▸ M.normalCore_le)) hne
  have h1 := M.index_normalCore_dvd_factorial_index
  rw [hcore, Subgroup.index_bot, card_alt7] at h1
  have hmul := M.card_mul_index
  rw [card_alt7] at hmul
  have hpos : 840 ≤ Nat.card M := Nat.le_of_dvd Nat.card_pos h840
  have hidx : M.index ≤ 3 := by
    by_contra h
    push Not at h
    nlinarith
  have hfac : M.index.factorial ≤ (3 : ℕ).factorial := Nat.factorial_le hidx
  have h6 : (3 : ℕ).factorial = 6 := by decide
  have := Nat.le_of_dvd (Nat.factorial_pos _) h1
  omega

end CFSG.Quasithin.E6.Alt.A7
