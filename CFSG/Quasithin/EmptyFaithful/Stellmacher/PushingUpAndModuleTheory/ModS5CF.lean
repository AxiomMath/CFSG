module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.PushingUpAndModuleTheory.ModS5Base
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.PushingUpAndModuleTheory.IrredClassification

public section

namespace CFSG.Quasithin.F53Mod

open Equiv

private theorem alt5_orders : ∀ σ : Perm (Fin 5), Perm.sign σ = 1 → σ ≠ 1 →
    (σ ^ 2 = 1 ∧ σ ^ 5 ≠ 1) ∨ (σ ^ 2 ≠ 1 ∧ σ ^ 3 = 1 ∧ σ ^ 5 ≠ 1) ∨
    (σ ^ 2 ≠ 1 ∧ σ ^ 3 ≠ 1 ∧ σ ^ 4 ≠ 1 ∧ σ ^ 5 = 1) := by decide +kernel

@[expose] def cfm (a : Perm (Fin 5)) : ℕ := if a ^ 5 = 1 then 16 else 4

theorem cfm_le_idx_of_irred {a : Perm (Fin 5)} (ha : a ∈ alternatingGroup (Fin 5)) (ha1 : a ≠ 1) :
    cfm a ≤ idx orth a ∧ cfm a ≤ idx nat a := by
  have hs := Perm.mem_alternatingGroup.mp ha
  unfold cfm
  rcases alt5_orders a hs ha1 with ⟨h2, h5⟩ | ⟨h2, h3, h5⟩ | ⟨h2, h3, h4, h5⟩
  · simp only [idx_orth, idx_nat, ha1, h2, h5, hs, ↓reduceIte]
    omega
  · simp only [idx_orth, idx_nat, ha1, h2, h3, h5, ↓reduceIte]
    omega
  · simp only [idx_orth, idx_nat, ha1, h2, h3, h4, h5, ↓reduceIte]
    omega

private theorem exists_moved {M : Model 5} (hA : fixW M (alternatingGroup (Fin 5)) ≠ ⊤) :
    ∃ σ w, M.act σ w ≠ w := by
  by_contra h
  push Not at h
  exact hA (eq_top_iff.mpr fun w _ b _ => h b w)

private theorem card_lt_of_ne_top {G : Type*} [Group G] [Finite G] {U : Subgroup G} (h : U ≠ ⊤) :
    Nat.card U < Nat.card G := by
  have h1 := Subgroup.card_mul_index U
  have h2 : U.index ≠ 1 := fun h' => h (Subgroup.index_eq_one.mp h')
  have h3 : U.index ≠ 0 := Subgroup.FiniteIndex.index_ne_zero
  have h4 : 0 < Nat.card U := Nat.card_pos
  nlinarith [Nat.pos_of_ne_zero h3, show 2 ≤ U.index by omega]

private theorem index_lt_card_of_ne_bot {G : Type*} [Group G] [Finite G] {U : Subgroup G}
    (h : U ≠ ⊥) : U.index < Nat.card G := by
  have h1 := Subgroup.card_mul_index U
  have h2 : Nat.card U ≠ 1 := fun h' => h (Subgroup.card_eq_one.mp h')
  have h4 : 0 < Nat.card U := Nat.card_pos
  have h3 : 0 < U.index := Nat.pos_of_ne_zero Subgroup.FiniteIndex.index_ne_zero
  nlinarith [show 2 ≤ Nat.card U by omega]

private theorem fixW_alt_eq_top_of_trivial {M : Model 5} {U : Subgroup M.W} (hU : IsInvSub M ⊤ U)
    (h1 : fixW (M.restrict U hU) (alternatingGroup (Fin 5)) = ⊤)
    (h2 : fixW (M.quot U hU) (alternatingGroup (Fin 5)) = ⊤) :
    fixW M (alternatingGroup (Fin 5)) = ⊤ := by
  have h1' : (fixW M (alternatingGroup (Fin 5))).subgroupOf U = ⊤ := by
    rw [← fixW_restrict]; exact h1
  refine bf7 alt5_perfect (Subgroup.subgroupOf_eq_top.mp h1') fun w b hb => ?_
  have : M.projQuot U hU w ∈ fixW (M.quot U hU) (alternatingGroup (Fin 5)) := by
    rw [h2]; trivial
  exact (M.projQuot_mem_fixW_iff U hU _ w).mp this b hb

private theorem cf_aux : ∀ (k : ℕ) (M : Model 5), Nat.card M.W ≤ k →
    fixW M (alternatingGroup (Fin 5)) ≠ ⊤ → ∀ a ∈ alternatingGroup (Fin 5), a ≠ 1 →
    cfm a ≤ idx M a := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro M hk hA a ha ha1
    by_cases hirr : M.IsIrred
    · rcases model5_irred_classification M hirr (exists_moved hA) with h | h
      · obtain ⟨e⟩ := h
        rw [← e.idx_eq]; exact (cfm_le_idx_of_irred ha ha1).1
      · obtain ⟨e⟩ := h
        rw [← e.idx_eq]; exact (cfm_le_idx_of_irred ha ha1).2
    · have hnt : ∃ w : M.W, w ≠ 1 := by
        obtain ⟨σ, w, hw⟩ := exists_moved hA
        exact ⟨w, fun h => hw (by rw [h, map_one])⟩
      have hnot : ¬ ∀ U : Subgroup M.W, IsInvSub M ⊤ U → U = ⊥ ∨ U = ⊤ := fun h => hirr ⟨hnt, h⟩
      push Not at hnot
      obtain ⟨U, hU, hbot, htop⟩ := hnot
      have hc1 : Nat.card (M.restrict U hU).W < Nat.card M.W := card_lt_of_ne_top htop
      have hc2 : Nat.card (M.quot U hU).W < Nat.card M.W := index_lt_card_of_ne_bot hbot
      by_cases h1 : fixW (M.restrict U hU) (alternatingGroup (Fin 5)) = ⊤
      · by_cases h2 : fixW (M.quot U hU) (alternatingGroup (Fin 5)) = ⊤
        · exact absurd (fixW_alt_eq_top_of_trivial hU h1 h2) hA
        · exact le_trans (ih _ (by omega) (M.quot U hU) le_rfl h2 a ha ha1) (idx_quot_le M U hU a)
      · exact le_trans (ih _ (by omega) (M.restrict U hU) le_rfl h1 a ha ha1)
          (idx_restrict_le M U hU a)

theorem cf (M : Model 5) (hA : fixW M (alternatingGroup (Fin 5)) ≠ ⊤) {a : Perm (Fin 5)}
    (ha : a ∈ alternatingGroup (Fin 5)) (ha1 : a ≠ 1) : cfm a ≤ idx M a :=
  cf_aux _ M le_rfl hA a ha ha1

theorem cf_small (M : Model 5) (hA : fixW M (alternatingGroup (Fin 5)) ≠ ⊤) {a : Perm (Fin 5)}
    (ha : a ∈ alternatingGroup (Fin 5)) (ha1 : a ≠ 1) (h : a ^ 5 ≠ 1) : 4 ≤ idx M a := by
  have := cf M hA ha ha1
  simpa only [cfm, h, ↓reduceIte] using this

theorem index_S5Syl : S5Syl.index = 15 := by
  have h := Subgroup.card_mul_index S5Syl
  rw [card_S5Syl, Nat.card_perm, Nat.card_eq_fintype_card, Fintype.card_fin] at h
  norm_num [Nat.factorial] at h
  omega

theorem odd_relIndex_S5Syl : Odd (S5Syl.relIndex ⊤) := by
  rw [Subgroup.relIndex_top_right, index_S5Syl]
  decide

end CFSG.Quasithin.F53Mod
