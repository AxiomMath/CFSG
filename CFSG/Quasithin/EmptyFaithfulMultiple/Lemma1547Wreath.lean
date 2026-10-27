module

public import CFSG.Quasithin.EmptyFaithfulMultiple.Inputs2

public section

namespace CFSG.Quasithin.EmptyFaithfulMultiple

namespace L1547

theorem wreath_block_injective {σ : Equiv.Perm (Fin 8)} (hσ : σ ∈ wreathSFourTwo) (b : ℕ)
    (hb : b < 2) :
    Function.Injective (fun i : Fin 4 =>
      (⟨(σ ⟨i.val + 4 * b, by omega⟩).val % 4, Nat.mod_lt _ (by norm_num)⟩ : Fin 4)) := by
  intro i j hij
  simp only [Fin.mk.injEq] at hij
  have hq := (hσ ⟨i.val + 4 * b, by omega⟩ ⟨j.val + 4 * b, by omega⟩).mp (by
    show (i.val + 4 * b) / 4 = (j.val + 4 * b) / 4
    omega)
  have heq : σ ⟨i.val + 4 * b, by omega⟩ = σ ⟨j.val + 4 * b, by omega⟩ := by
    apply Fin.ext
    have h1 := Nat.div_add_mod (σ ⟨i.val + 4 * b, by omega⟩).val 4
    have h2 := Nat.div_add_mod (σ ⟨j.val + 4 * b, by omega⟩).val 4
    omega
  have := congrArg Fin.val (σ.injective heq)
  simp only at this
  exact Fin.ext (by omega)

theorem card_wreathSFourTwo_le : Nat.card wreathSFourTwo ≤ 1152 := by
  classical
  let f : (b : ℕ) → b < 2 → wreathSFourTwo → (Fin 4 ↪ Fin 4) := fun b hb σ =>
    ⟨_, wreath_block_injective σ.2 b hb⟩
  let F : wreathSFourTwo → Bool × (Fin 4 ↪ Fin 4) × (Fin 4 ↪ Fin 4) := fun σ =>
    (decide (((σ : Equiv.Perm (Fin 8)) 0).val / 4 = 0), f 0 (by norm_num) σ,
      f 1 (by norm_num) σ)
  have hF : Function.Injective F := by
    intro σ τ hστ
    simp only [F, Prod.mk.injEq] at hστ
    obtain ⟨h0, h1, h2⟩ := hστ
    have h0' : ((σ : Equiv.Perm (Fin 8)) 0).val / 4 = ((τ : Equiv.Perm (Fin 8)) 0).val / 4 := by
      have hs : ((σ : Equiv.Perm (Fin 8)) 0).val / 4 < 2 := by omega
      have ht : ((τ : Equiv.Perm (Fin 8)) 0).val / 4 < 2 := by omega
      by_cases hs0 : ((σ : Equiv.Perm (Fin 8)) 0).val / 4 = 0
      · simp only [hs0, decide_true] at h0
        have := of_decide_eq_true h0.symm
        omega
      · simp only [hs0, decide_false] at h0
        have := of_decide_eq_false h0.symm
        omega
    apply Subtype.ext
    ext k
    have hblk : ∀ ρ : wreathSFourTwo, ((ρ : Equiv.Perm (Fin 8)) k).val / 4 =
        if k.val / 4 = 0 then ((ρ : Equiv.Perm (Fin 8)) 0).val / 4
        else 1 - ((ρ : Equiv.Perm (Fin 8)) 0).val / 4 := by
      intro ρ
      have hk := ρ.2 k 0
      have hlt : ((ρ : Equiv.Perm (Fin 8)) k).val / 4 < 2 := by omega
      have hlt0 : ((ρ : Equiv.Perm (Fin 8)) 0).val / 4 < 2 := by omega
      split_ifs with hk0
      · exact hk.mp (by simpa using hk0)
      · have : ((ρ : Equiv.Perm (Fin 8)) k).val / 4 ≠ ((ρ : Equiv.Perm (Fin 8)) 0).val / 4 :=
          fun h => hk0 (by simpa using hk.mpr h)
        omega
    have hres : ((σ : Equiv.Perm (Fin 8)) k).val % 4 = ((τ : Equiv.Perm (Fin 8)) k).val % 4 := by
      have hk8 := k.2
      by_cases hk4 : k.val < 4
      · have := congrArg (fun e : Fin 4 ↪ Fin 4 => (e ⟨k.val, hk4⟩).val) h1
        simp only [f, Function.Embedding.coeFn_mk] at this
        have hk' : (⟨(⟨k.val, hk4⟩ : Fin 4).val + 4 * 0, by omega⟩ : Fin 8) = k :=
          Fin.ext (by simp)
        rwa [hk'] at this
      · have := congrArg (fun e : Fin 4 ↪ Fin 4 => (e ⟨k.val - 4, by omega⟩).val) h2
        simp only [f, Function.Embedding.coeFn_mk] at this
        have hk' : (⟨(⟨k.val - 4, by omega⟩ : Fin 4).val + 4 * 1, by omega⟩ : Fin 8) = k :=
          Fin.ext (by simp; omega)
        rwa [hk'] at this
    have hσk := hblk σ
    have hτk := hblk τ
    rw [h0'] at hσk
    rw [← hτk] at hσk
    have e1 := Nat.div_add_mod ((σ : Equiv.Perm (Fin 8)) k).val 4
    have e2 := Nat.div_add_mod ((τ : Equiv.Perm (Fin 8)) k).val 4
    omega
  calc Nat.card wreathSFourTwo ≤ Nat.card (Bool × (Fin 4 ↪ Fin 4) × (Fin 4 ↪ Fin 4)) :=
        Nat.card_le_card_of_injective F hF
    _ = 1152 := by
      rw [Nat.card_eq_fintype_card]
      simp [Fintype.card_embedding_eq]

end L1547

end CFSG.Quasithin.EmptyFaithfulMultiple
