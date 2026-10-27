module

public import Mathlib.GroupTheory.Perm.ViaEmbedding
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Data.Nat.Totient
public import Mathlib.Data.Sym.Sym2.Init
public import Mathlib.GroupTheory.Perm.Support
public import Mathlib.Tactic.Group
public import Mathlib.Tactic.IntervalCases
public import Mathlib.Tactic.NormNum.GCD

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open Equiv Equiv.Perm Subgroup

theorem w85g_orderOf_eq_six_of_pow {G : Type*} [Group G] {f : G}
    (h6 : f ^ 6 = 1) (h2 : f ^ 2 ≠ 1) (h3 : f ^ 3 ≠ 1) : orderOf f = 6 := by
  have hdvd : orderOf f ∣ 6 := orderOf_dvd_of_pow_eq_one h6
  have hle : orderOf f ≤ 6 := Nat.le_of_dvd (by norm_num) hdvd
  have hpos : 0 < orderOf f := by
    rw [orderOf_pos_iff]
    exact isOfFinOrder_iff_pow_eq_one.mpr ⟨6, by norm_num, h6⟩
  have h1 : orderOf f ≠ 1 := by
    intro h
    exact h2 (by rw [orderOf_eq_one_iff.mp h]; simp)
  have h2' : orderOf f ≠ 2 := by
    intro h
    exact h2 (by rw [← h]; exact pow_orderOf_eq_one f)
  have h3' : orderOf f ≠ 3 := by
    intro h
    exact h3 (by rw [← h]; exact pow_orderOf_eq_one f)
  have h4 : orderOf f ≠ 4 := by
    intro h
    obtain ⟨k, hk⟩ : 4 ∣ 6 := h ▸ hdvd
    omega
  have h5 : orderOf f ≠ 5 := by
    intro h
    obtain ⟨k, hk⟩ : 5 ∣ 6 := h ▸ hdvd
    omega
  omega

theorem w85g_injective_of_nodup7 {α : Type} [DecidableEq α] {a1 b1 a2 b2 a3 b3 x : α}
    (h : [a1, b1, a2, b2, a3, b3, x].Nodup) :
    Function.Injective (![a1, b1, a2, b2, a3, b3, x] : Fin 7 → α) := by
  intro i j hij
  fin_cases i <;> fin_cases j <;>
    simp_all [List.nodup_cons, List.mem_cons, List.mem_singleton]

theorem w85g_exists_fixed_embedding {α : Type} [Fintype α] [DecidableEq α] {τ : Perm α} (hτ : τ * τ
    = 1)
    (h6 : 6 ≤ τ.support.card) {x : α} (hx : τ x = x) :
    ∃ p : Fin 7 ↪ α,
      ∀ i, τ (p i) = p ((swap 0 1 * swap 2 3 * swap 4 5 : Perm (Fin 7)) i) := by
  have hττ : ∀ y, τ (τ y) = y := by
    intro y
    have := congrArg (fun g : Perm α => g y) hτ
    simpa [Equiv.Perm.mul_apply] using this
  have hpartner : ∀ y ∈ τ.support, τ y ∈ τ.support := by
    intro y hy
    rw [Equiv.Perm.mem_support] at hy ⊢
    rw [hττ y]
    exact Ne.symm hy
  obtain ⟨a1, ha1⟩ := Finset.card_pos.mp (by omega : 0 < τ.support.card)
  have ha1ne : τ a1 ≠ a1 := (Equiv.Perm.mem_support).mp ha1
  have hb1 : τ a1 ∈ τ.support.erase a1 := by
    rw [Finset.mem_erase]
    exact ⟨ha1ne, hpartner a1 ha1⟩
  have hcard1 : 0 < ((τ.support.erase a1).erase (τ a1)).card := by
    rw [Finset.card_erase_of_mem hb1, Finset.card_erase_of_mem ha1]
    omega
  obtain ⟨a2, ha2⟩ := Finset.card_pos.mp hcard1
  have ha2mem : a2 ∈ (τ.support.erase a1).erase (τ a1) := ha2
  rw [Finset.mem_erase] at ha2
  obtain ⟨ha2b1, ha2⟩ := ha2
  rw [Finset.mem_erase] at ha2
  obtain ⟨ha2a1, ha2supp⟩ := ha2
  have ha2ne : τ a2 ≠ a2 := (Equiv.Perm.mem_support).mp ha2supp
  have hb2 : τ a2 ∈ (τ.support.erase a1).erase (τ a1) := by
    rw [Finset.mem_erase]
    refine ⟨?_, ?_⟩
    · intro h
      exact ha2a1 (τ.injective h)
    · rw [Finset.mem_erase]
      exact ⟨fun h => ha2b1 (by rw [← hττ a2, h]), hpartner a2 ha2supp⟩
  have hb2' : τ a2 ∈ ((τ.support.erase a1).erase (τ a1)).erase a2 := by
    rw [Finset.mem_erase]
    exact ⟨ha2ne, hb2⟩
  have hcard2 : 0 < ((((τ.support.erase a1).erase (τ a1)).erase a2).erase (τ a2)).card := by
    rw [Finset.card_erase_of_mem hb2', Finset.card_erase_of_mem ha2mem]
    rw [Finset.card_erase_of_mem hb1, Finset.card_erase_of_mem ha1]
    omega
  obtain ⟨a3, ha3⟩ := Finset.card_pos.mp hcard2
  rw [Finset.mem_erase] at ha3
  obtain ⟨ha3b2, ha3⟩ := ha3
  rw [Finset.mem_erase] at ha3
  obtain ⟨ha3a2, ha3⟩ := ha3
  rw [Finset.mem_erase] at ha3
  obtain ⟨ha3b1, ha3⟩ := ha3
  rw [Finset.mem_erase] at ha3
  obtain ⟨ha3a1, ha3supp⟩ := ha3
  have ha3ne : τ a3 ≠ a3 := (Equiv.Perm.mem_support).mp ha3supp
  have hxnot : x ∉ τ.support := by
    rw [Equiv.Perm.mem_support]
    exact fun h => h hx
  have hb3mem : τ a3 ∈ τ.support := hpartner a3 ha3supp
  have hb1mem : τ a1 ∈ τ.support := hpartner a1 ha1
  have hb2mem : τ a2 ∈ τ.support := hpartner a2 ha2supp
  have hτpre : ∀ {y z : α}, y = τ z → z = τ y := by
    intro y z h
    rw [h]
    exact (hττ z).symm
  have h11 : a1 ≠ τ a1 := ha1ne.symm
  have h12 : a1 ≠ a2 := ha2a1.symm
  have h13 : a1 ≠ τ a2 := fun h => ha2b1 (hτpre h)
  have h14 : a1 ≠ a3 := ha3a1.symm
  have h15 : a1 ≠ τ a3 := fun h => ha3b1 (hτpre h)
  have h16 : a1 ≠ x := fun h => hxnot (h ▸ ha1)
  have h21 : τ a1 ≠ a2 := ha2b1.symm
  have h22 : τ a1 ≠ τ a2 := fun h => ha2a1 (τ.injective h).symm
  have h23 : τ a1 ≠ a3 := ha3b1.symm
  have h24 : τ a1 ≠ τ a3 := fun h => ha3a1 (τ.injective h).symm
  have h25 : τ a1 ≠ x := fun h => hxnot (h ▸ hb1mem)
  have h31 : a2 ≠ τ a2 := ha2ne.symm
  have h32 : a2 ≠ a3 := ha3a2.symm
  have h33 : a2 ≠ τ a3 := fun h => ha3b2 (hτpre h)
  have h34 : a2 ≠ x := fun h => hxnot (h ▸ ha2supp)
  have h41 : τ a2 ≠ a3 := ha3b2.symm
  have h42 : τ a2 ≠ τ a3 := fun h => ha3a2 (τ.injective h).symm
  have h43 : τ a2 ≠ x := fun h => hxnot (h ▸ hb2mem)
  have h51 : a3 ≠ τ a3 := ha3ne.symm
  have h52 : a3 ≠ x := fun h => hxnot (h ▸ ha3supp)
  have h53 : τ a3 ≠ x := fun h => hxnot (h ▸ hb3mem)
  have hnd : [a1, τ a1, a2, τ a2, a3, τ a3, x].Nodup := by
    simp only [List.nodup_cons, List.not_mem_nil, not_false_eq_true, and_true, List.mem_cons,
      List.mem_singleton, not_or]
    tauto
  have e0 : (swap 0 1 * swap 2 3 * swap 4 5 : Perm (Fin 7)) 0 = 1 := by decide
  have e1 : (swap 0 1 * swap 2 3 * swap 4 5 : Perm (Fin 7)) 1 = 0 := by decide
  have e2 : (swap 0 1 * swap 2 3 * swap 4 5 : Perm (Fin 7)) 2 = 3 := by decide
  have e3 : (swap 0 1 * swap 2 3 * swap 4 5 : Perm (Fin 7)) 3 = 2 := by decide
  have e4 : (swap 0 1 * swap 2 3 * swap 4 5 : Perm (Fin 7)) 4 = 5 := by decide
  have e5 : (swap 0 1 * swap 2 3 * swap 4 5 : Perm (Fin 7)) 5 = 4 := by decide
  have e6 : (swap 0 1 * swap 2 3 * swap 4 5 : Perm (Fin 7)) 6 = 6 := by decide
  let emb : Fin 7 ↪ α := ⟨![a1, τ a1, a2, τ a2, a3, τ a3, x], w85g_injective_of_nodup7 hnd⟩
  refine ⟨emb, ?_⟩
  intro i
  fin_cases i <;> simp [emb, hττ, hx, e0, e1, e2, e3, e4, e5, e6]

theorem w85g_injective_of_nodup10 {α : Type} [DecidableEq α]
    {a1 b1 a2 b2 a3 b3 a4 b4 a5 b5 : α}
    (h : [a1, b1, a2, b2, a3, b3, a4, b4, a5, b5].Nodup) :
    Function.Injective (![a1, b1, a2, b2, a3, b3, a4, b4, a5, b5] : Fin 10 → α) := by
  intro i j hij
  fin_cases i <;> fin_cases j <;>
    simp_all [List.nodup_cons, List.mem_cons, List.mem_singleton]

theorem w85g_exists_free_embedding {α : Type} [Fintype α] [DecidableEq α] {τ : Perm α} (hτ : τ * τ =
    1)
    (h10 : 10 ≤ τ.support.card) :
    ∃ p : Fin 10 ↪ α, ∀ i, τ (p i) =
      p ((swap 0 1 * swap 2 3 * swap 4 5 * swap 6 7 * swap 8 9 : Perm (Fin 10)) i) := by
  have hττ : ∀ y, τ (τ y) = y := by
    intro y
    have := congrArg (fun g : Perm α => g y) hτ
    simpa [Equiv.Perm.mul_apply] using this
  have hpartner : ∀ y ∈ τ.support, τ y ∈ τ.support := by
    intro y hy
    rw [Equiv.Perm.mem_support] at hy ⊢
    rw [hττ y]
    exact Ne.symm hy
  obtain ⟨a1, ha1⟩ := Finset.card_pos.mp (by omega : 0 < τ.support.card)
  have ha1supp : a1 ∈ τ.support := ha1
  have ha1mem : a1 ∈ τ.support := ha1supp
  have ha1ne : τ a1 ≠ a1 := (Equiv.Perm.mem_support).mp ha1supp
  have hb1mem : τ a1 ∈ τ.support := hpartner a1 ha1supp
  have hb1 : τ a1 ∈ τ.support.erase a1 := by
    rw [Finset.mem_erase]
    exact ⟨ha1ne, hb1mem⟩
  have hb1' : τ a1 ∈ (τ.support).erase a1 := hb1
  have hcard1 : 0 < (((τ.support).erase a1).erase (τ a1)).card := by
    rw [Finset.card_erase_of_mem hb1', Finset.card_erase_of_mem ha1mem]
    omega
  obtain ⟨a2, ha2⟩ := Finset.card_pos.mp hcard1
  have ha2mem : a2 ∈ ((τ.support).erase a1).erase (τ a1) := ha2
  rw [Finset.mem_erase] at ha2
  obtain ⟨ha2b1, ha2⟩ := ha2
  rw [Finset.mem_erase] at ha2
  obtain ⟨ha2a1, ha2⟩ := ha2
  have ha2supp : a2 ∈ τ.support := ha2
  have ha2ne : τ a2 ≠ a2 := (Equiv.Perm.mem_support).mp ha2supp
  have hb2mem : τ a2 ∈ τ.support := hpartner a2 ha2supp
  have hb2 : τ a2 ∈ ((τ.support).erase a1).erase (τ a1) := by
    rw [Finset.mem_erase]
    refine ⟨?_, ?_⟩
    · intro h; exact ha2a1 (τ.injective h)
    · rw [Finset.mem_erase]
      refine ⟨?_, ?_⟩
      · intro h; exact ha2b1 (by rw [← hττ a2]; exact congrArg τ h)
      exact hb2mem
  have hb2' : τ a2 ∈ (((τ.support).erase a1).erase (τ a1)).erase a2 := by
    rw [Finset.mem_erase]
    exact ⟨ha2ne, hb2⟩
  have hcard2 : 0 < (((((τ.support).erase a1).erase (τ a1)).erase a2).erase (τ a2)).card := by
    rw [Finset.card_erase_of_mem hb2', Finset.card_erase_of_mem ha2mem,
        Finset.card_erase_of_mem hb1', Finset.card_erase_of_mem ha1mem]
    omega
  obtain ⟨a3, ha3⟩ := Finset.card_pos.mp hcard2
  have ha3mem : a3 ∈ ((((τ.support).erase a1).erase (τ a1)).erase a2).erase (τ a2) := ha3
  rw [Finset.mem_erase] at ha3
  obtain ⟨ha3b2, ha3⟩ := ha3
  rw [Finset.mem_erase] at ha3
  obtain ⟨ha3a2, ha3⟩ := ha3
  rw [Finset.mem_erase] at ha3
  obtain ⟨ha3b1, ha3⟩ := ha3
  rw [Finset.mem_erase] at ha3
  obtain ⟨ha3a1, ha3⟩ := ha3
  have ha3supp : a3 ∈ τ.support := ha3
  have ha3ne : τ a3 ≠ a3 := (Equiv.Perm.mem_support).mp ha3supp
  have hb3mem : τ a3 ∈ τ.support := hpartner a3 ha3supp
  have hb3 : τ a3 ∈ ((((τ.support).erase a1).erase (τ a1)).erase a2).erase (τ a2) := by
    rw [Finset.mem_erase]
    refine ⟨?_, ?_⟩
    · intro h; exact ha3a2 (τ.injective h)
    · rw [Finset.mem_erase]
      refine ⟨?_, ?_⟩
      · intro h; exact ha3b2 (by rw [← hττ a3]; exact congrArg τ h)
      rw [Finset.mem_erase]
      refine ⟨?_, ?_⟩
      · intro h; exact ha3a1 (τ.injective h)
      · rw [Finset.mem_erase]
        refine ⟨?_, ?_⟩
        · intro h; exact ha3b1 (by rw [← hττ a3]; exact congrArg τ h)
        exact hb3mem
  have hb3' : τ a3 ∈ (((((τ.support).erase a1).erase (τ a1)).erase a2).erase (τ a2)).erase a3 := by
    rw [Finset.mem_erase]
    exact ⟨ha3ne, hb3⟩
  have hcard3 : 0 < (((((((τ.support).erase a1).erase (τ a1)).erase a2).erase (τ a2)).erase
      a3).erase (τ a3)).card := by
    rw [Finset.card_erase_of_mem hb3', Finset.card_erase_of_mem ha3mem,
        Finset.card_erase_of_mem hb2', Finset.card_erase_of_mem ha2mem,
        Finset.card_erase_of_mem hb1', Finset.card_erase_of_mem ha1mem]
    omega
  obtain ⟨a4, ha4⟩ := Finset.card_pos.mp hcard3
  have ha4mem : a4 ∈ ((((((τ.support).erase a1).erase (τ a1)).erase a2).erase (τ a2)).erase
      a3).erase (τ a3) := ha4
  rw [Finset.mem_erase] at ha4
  obtain ⟨ha4b3, ha4⟩ := ha4
  rw [Finset.mem_erase] at ha4
  obtain ⟨ha4a3, ha4⟩ := ha4
  rw [Finset.mem_erase] at ha4
  obtain ⟨ha4b2, ha4⟩ := ha4
  rw [Finset.mem_erase] at ha4
  obtain ⟨ha4a2, ha4⟩ := ha4
  rw [Finset.mem_erase] at ha4
  obtain ⟨ha4b1, ha4⟩ := ha4
  rw [Finset.mem_erase] at ha4
  obtain ⟨ha4a1, ha4⟩ := ha4
  have ha4supp : a4 ∈ τ.support := ha4
  have ha4ne : τ a4 ≠ a4 := (Equiv.Perm.mem_support).mp ha4supp
  have hb4mem : τ a4 ∈ τ.support := hpartner a4 ha4supp
  have hb4 : τ a4 ∈ ((((((τ.support).erase a1).erase (τ a1)).erase a2).erase (τ a2)).erase a3).erase
      (τ a3) := by
    rw [Finset.mem_erase]
    refine ⟨?_, ?_⟩
    · intro h; exact ha4a3 (τ.injective h)
    · rw [Finset.mem_erase]
      refine ⟨?_, ?_⟩
      · intro h; exact ha4b3 (by rw [← hττ a4]; exact congrArg τ h)
      rw [Finset.mem_erase]
      refine ⟨?_, ?_⟩
      · intro h; exact ha4a2 (τ.injective h)
      · rw [Finset.mem_erase]
        refine ⟨?_, ?_⟩
        · intro h; exact ha4b2 (by rw [← hττ a4]; exact congrArg τ h)
        rw [Finset.mem_erase]
        refine ⟨?_, ?_⟩
        · intro h; exact ha4a1 (τ.injective h)
        · rw [Finset.mem_erase]
          refine ⟨?_, ?_⟩
          · intro h; exact ha4b1 (by rw [← hττ a4]; exact congrArg τ h)
          exact hb4mem
  have hb4' : τ a4 ∈ (((((((τ.support).erase a1).erase (τ a1)).erase a2).erase (τ a2)).erase
      a3).erase (τ a3)).erase a4 := by
    rw [Finset.mem_erase]
    exact ⟨ha4ne, hb4⟩
  have hcard4 : 0 < (((((((((τ.support).erase a1).erase (τ a1)).erase a2).erase (τ a2)).erase
      a3).erase (τ a3)).erase a4).erase (τ a4)).card := by
    rw [Finset.card_erase_of_mem hb4', Finset.card_erase_of_mem ha4mem,
        Finset.card_erase_of_mem hb3', Finset.card_erase_of_mem ha3mem,
        Finset.card_erase_of_mem hb2', Finset.card_erase_of_mem ha2mem,
        Finset.card_erase_of_mem hb1', Finset.card_erase_of_mem ha1mem]
    omega
  obtain ⟨a5, ha5⟩ := Finset.card_pos.mp hcard4
  have ha5mem : a5 ∈ ((((((((τ.support).erase a1).erase (τ a1)).erase a2).erase (τ a2)).erase
      a3).erase (τ a3)).erase a4).erase (τ a4) := ha5
  rw [Finset.mem_erase] at ha5
  obtain ⟨ha5b4, ha5⟩ := ha5
  rw [Finset.mem_erase] at ha5
  obtain ⟨ha5a4, ha5⟩ := ha5
  rw [Finset.mem_erase] at ha5
  obtain ⟨ha5b3, ha5⟩ := ha5
  rw [Finset.mem_erase] at ha5
  obtain ⟨ha5a3, ha5⟩ := ha5
  rw [Finset.mem_erase] at ha5
  obtain ⟨ha5b2, ha5⟩ := ha5
  rw [Finset.mem_erase] at ha5
  obtain ⟨ha5a2, ha5⟩ := ha5
  rw [Finset.mem_erase] at ha5
  obtain ⟨ha5b1, ha5⟩ := ha5
  rw [Finset.mem_erase] at ha5
  obtain ⟨ha5a1, ha5⟩ := ha5
  have ha5supp : a5 ∈ τ.support := ha5
  have ha5ne : τ a5 ≠ a5 := (Equiv.Perm.mem_support).mp ha5supp
  have hb5mem : τ a5 ∈ τ.support := hpartner a5 ha5supp
  have hb5 : τ a5 ∈ ((((((((τ.support).erase a1).erase (τ a1)).erase a2).erase (τ a2)).erase
      a3).erase (τ a3)).erase a4).erase (τ a4) := by
    rw [Finset.mem_erase]
    refine ⟨?_, ?_⟩
    · intro h; exact ha5a4 (τ.injective h)
    · rw [Finset.mem_erase]
      refine ⟨?_, ?_⟩
      · intro h; exact ha5b4 (by rw [← hττ a5]; exact congrArg τ h)
      rw [Finset.mem_erase]
      refine ⟨?_, ?_⟩
      · intro h; exact ha5a3 (τ.injective h)
      · rw [Finset.mem_erase]
        refine ⟨?_, ?_⟩
        · intro h; exact ha5b3 (by rw [← hττ a5]; exact congrArg τ h)
        rw [Finset.mem_erase]
        refine ⟨?_, ?_⟩
        · intro h; exact ha5a2 (τ.injective h)
        · rw [Finset.mem_erase]
          refine ⟨?_, ?_⟩
          · intro h; exact ha5b2 (by rw [← hττ a5]; exact congrArg τ h)
          rw [Finset.mem_erase]
          refine ⟨?_, ?_⟩
          · intro h; exact ha5a1 (τ.injective h)
          · rw [Finset.mem_erase]
            refine ⟨?_, ?_⟩
            · intro h; exact ha5b1 (by rw [← hττ a5]; exact congrArg τ h)
            exact hb5mem
  have hb5' : τ a5 ∈ (((((((((τ.support).erase a1).erase (τ a1)).erase a2).erase (τ a2)).erase
      a3).erase (τ a3)).erase a4).erase (τ a4)).erase a5 := by
    rw [Finset.mem_erase]
    exact ⟨ha5ne, hb5⟩
  have ha1b1 : a1 ≠ τ a1 := ha1ne.symm
  have ha2b2 : a2 ≠ τ a2 := ha2ne.symm
  have ha3b3 : a3 ≠ τ a3 := ha3ne.symm
  have ha4b4 : a4 ≠ τ a4 := ha4ne.symm
  have ha5b5 : a5 ≠ τ a5 := ha5ne.symm
  have hb2a1 : τ a2 ≠ a1 := fun h => ha2b1 (by rw [← hττ a2]; exact congrArg τ h)
  have hb2b1 : τ a2 ≠ τ a1 := fun h => ha2a1 (τ.injective h)
  have hb3a1 : τ a3 ≠ a1 := fun h => ha3b1 (by rw [← hττ a3]; exact congrArg τ h)
  have hb3b1 : τ a3 ≠ τ a1 := fun h => ha3a1 (τ.injective h)
  have hb3a2 : τ a3 ≠ a2 := fun h => ha3b2 (by rw [← hττ a3]; exact congrArg τ h)
  have hb3b2 : τ a3 ≠ τ a2 := fun h => ha3a2 (τ.injective h)
  have hb4a1 : τ a4 ≠ a1 := fun h => ha4b1 (by rw [← hττ a4]; exact congrArg τ h)
  have hb4b1 : τ a4 ≠ τ a1 := fun h => ha4a1 (τ.injective h)
  have hb4a2 : τ a4 ≠ a2 := fun h => ha4b2 (by rw [← hττ a4]; exact congrArg τ h)
  have hb4b2 : τ a4 ≠ τ a2 := fun h => ha4a2 (τ.injective h)
  have hb4a3 : τ a4 ≠ a3 := fun h => ha4b3 (by rw [← hττ a4]; exact congrArg τ h)
  have hb4b3 : τ a4 ≠ τ a3 := fun h => ha4a3 (τ.injective h)
  have hb5a1 : τ a5 ≠ a1 := fun h => ha5b1 (by rw [← hττ a5]; exact congrArg τ h)
  have hb5b1 : τ a5 ≠ τ a1 := fun h => ha5a1 (τ.injective h)
  have hb5a2 : τ a5 ≠ a2 := fun h => ha5b2 (by rw [← hττ a5]; exact congrArg τ h)
  have hb5b2 : τ a5 ≠ τ a2 := fun h => ha5a2 (τ.injective h)
  have hb5a3 : τ a5 ≠ a3 := fun h => ha5b3 (by rw [← hττ a5]; exact congrArg τ h)
  have hb5b3 : τ a5 ≠ τ a3 := fun h => ha5a3 (τ.injective h)
  have hb5a4 : τ a5 ≠ a4 := fun h => ha5b4 (by rw [← hττ a5]; exact congrArg τ h)
  have hb5b4 : τ a5 ≠ τ a4 := fun h => ha5a4 (τ.injective h)
  have f0 : a1 ≠ τ a1 := ha1b1
  have f1 : a1 ≠ a2 := (ha2a1).symm
  have f2 : a1 ≠ τ a2 := (hb2a1).symm
  have f3 : a1 ≠ a3 := (ha3a1).symm
  have f4 : a1 ≠ τ a3 := (hb3a1).symm
  have f5 : a1 ≠ a4 := (ha4a1).symm
  have f6 : a1 ≠ τ a4 := (hb4a1).symm
  have f7 : a1 ≠ a5 := (ha5a1).symm
  have f8 : a1 ≠ τ a5 := (hb5a1).symm
  have f9 : τ a1 ≠ a2 := (ha2b1).symm
  have f10 : τ a1 ≠ τ a2 := (hb2b1).symm
  have f11 : τ a1 ≠ a3 := (ha3b1).symm
  have f12 : τ a1 ≠ τ a3 := (hb3b1).symm
  have f13 : τ a1 ≠ a4 := (ha4b1).symm
  have f14 : τ a1 ≠ τ a4 := (hb4b1).symm
  have f15 : τ a1 ≠ a5 := (ha5b1).symm
  have f16 : τ a1 ≠ τ a5 := (hb5b1).symm
  have f17 : a2 ≠ τ a2 := ha2b2
  have f18 : a2 ≠ a3 := (ha3a2).symm
  have f19 : a2 ≠ τ a3 := (hb3a2).symm
  have f20 : a2 ≠ a4 := (ha4a2).symm
  have f21 : a2 ≠ τ a4 := (hb4a2).symm
  have f22 : a2 ≠ a5 := (ha5a2).symm
  have f23 : a2 ≠ τ a5 := (hb5a2).symm
  have f24 : τ a2 ≠ a3 := (ha3b2).symm
  have f25 : τ a2 ≠ τ a3 := (hb3b2).symm
  have f26 : τ a2 ≠ a4 := (ha4b2).symm
  have f27 : τ a2 ≠ τ a4 := (hb4b2).symm
  have f28 : τ a2 ≠ a5 := (ha5b2).symm
  have f29 : τ a2 ≠ τ a5 := (hb5b2).symm
  have f30 : a3 ≠ τ a3 := ha3b3
  have f31 : a3 ≠ a4 := (ha4a3).symm
  have f32 : a3 ≠ τ a4 := (hb4a3).symm
  have f33 : a3 ≠ a5 := (ha5a3).symm
  have f34 : a3 ≠ τ a5 := (hb5a3).symm
  have f35 : τ a3 ≠ a4 := (ha4b3).symm
  have f36 : τ a3 ≠ τ a4 := (hb4b3).symm
  have f37 : τ a3 ≠ a5 := (ha5b3).symm
  have f38 : τ a3 ≠ τ a5 := (hb5b3).symm
  have f39 : a4 ≠ τ a4 := ha4b4
  have f40 : a4 ≠ a5 := (ha5a4).symm
  have f41 : a4 ≠ τ a5 := (hb5a4).symm
  have f42 : τ a4 ≠ a5 := (ha5b4).symm
  have f43 : τ a4 ≠ τ a5 := (hb5b4).symm
  have f44 : a5 ≠ τ a5 := ha5b5
  have hnd : [a1, τ a1, a2, τ a2, a3, τ a3, a4, τ a4, a5, τ a5].Nodup := by
    simp only [List.nodup_cons, List.not_mem_nil, not_false_eq_true, and_true,
      List.mem_cons, List.mem_singleton, not_or]
    tauto
  have e0 : (swap 0 1 * swap 2 3 * swap 4 5 * swap 6 7 * swap 8 9 : Perm (Fin 10)) 0 =
      1 := by decide
  have e1 : (swap 0 1 * swap 2 3 * swap 4 5 * swap 6 7 * swap 8 9 : Perm (Fin 10)) 1 =
      0 := by decide
  have e2 : (swap 0 1 * swap 2 3 * swap 4 5 * swap 6 7 * swap 8 9 : Perm (Fin 10)) 2 =
      3 := by decide
  have e3 : (swap 0 1 * swap 2 3 * swap 4 5 * swap 6 7 * swap 8 9 : Perm (Fin 10)) 3 =
      2 := by decide
  have e4 : (swap 0 1 * swap 2 3 * swap 4 5 * swap 6 7 * swap 8 9 : Perm (Fin 10)) 4 =
      5 := by decide
  have e5 : (swap 0 1 * swap 2 3 * swap 4 5 * swap 6 7 * swap 8 9 : Perm (Fin 10)) 5 =
      4 := by decide
  have e6 : (swap 0 1 * swap 2 3 * swap 4 5 * swap 6 7 * swap 8 9 : Perm (Fin 10)) 6 =
      7 := by decide
  have e7 : (swap 0 1 * swap 2 3 * swap 4 5 * swap 6 7 * swap 8 9 : Perm (Fin 10)) 7 =
      6 := by decide
  have e8 : (swap 0 1 * swap 2 3 * swap 4 5 * swap 6 7 * swap 8 9 : Perm (Fin 10)) 8 =
      9 := by decide
  have e9 : (swap 0 1 * swap 2 3 * swap 4 5 * swap 6 7 * swap 8 9 : Perm (Fin 10)) 9 =
      8 := by decide
  let emb : Fin 10 ↪ α := ⟨![a1, τ a1, a2, τ a2, a3, τ a3, a4, τ a4, a5, τ a5],
    w85g_injective_of_nodup10 hnd⟩
  refine ⟨emb, ?_⟩
  intro i
  fin_cases i <;>
    simp [emb, hττ, e0, e1, e2, e3, e4, e5, e6, e7, e8, e9]

theorem w85g_orderOf_six_fixed {α : Type} [DecidableEq α] {τ : Perm α} (hτ : τ * τ = 1)
    {p : Fin 7 → α} (hp : Function.Injective p)
    (hτp : ∀ i, τ (p i) = p ((swap 0 1 * swap 2 3 * swap 4 5 : Perm (Fin 7)) i)) :
    ∃ σ : Perm α, orderOf (τ * (σ * τ * σ⁻¹)) = 6 := by
  have idx : ∀ i j : Fin 7, (swap 0 1 * swap 2 3 * swap 4 5 : Perm (Fin 7)) i = j →
      τ (p i) = p j := by
    intro i j hij
    rw [← hij]
    exact hτp i
  have h1 : τ (p 1) = p 0 := idx 1 0 (by decide)
  have h3 : τ (p 3) = p 2 := idx 3 2 (by decide)
  have h5 : τ (p 5) = p 4 := idx 5 4 (by decide)
  have h6 : τ (p 6) = p 6 := idx 6 6 (by decide)
  have hconj1 : τ * swap (p 1) (p 3) * τ = swap (p 0) (p 2) := by
    rw [mul_swap_eq_swap_mul τ (p 1) (p 3), h1, h3,
      mul_assoc (swap (p 0) (p 2)) τ τ, hτ, mul_one]
  have hconj2 : τ * swap (p 5) (p 6) * τ = swap (p 4) (p 6) := by
    rw [mul_swap_eq_swap_mul τ (p 5) (p 6), h5, h6,
      mul_assoc (swap (p 4) (p 6)) τ τ, hτ, mul_one]
  have hconj : τ * (swap (p 1) (p 3) * swap (p 5) (p 6)) * τ =
      swap (p 0) (p 2) * swap (p 4) (p 6) := by
    rw [show τ * (swap (p 1) (p 3) * swap (p 5) (p 6)) * τ =
        (τ * swap (p 1) (p 3) * τ) * (τ * swap (p 5) (p 6) * τ) by
      rw [show (τ * swap (p 1) (p 3) * τ) * (τ * swap (p 5) (p 6) * τ) =
        τ * swap (p 1) (p 3) * (τ * τ) * swap (p 5) (p 6) * τ by group]
      rw [hτ]
      group]
    rw [hconj1, hconj2]
  have hσinv : (swap (p 1) (p 3) * swap (p 5) (p 6) : Perm α)⁻¹ =
      swap (p 5) (p 6) * swap (p 1) (p 3) := by
    rw [mul_inv_rev, Equiv.swap_inv, Equiv.swap_inv]
  let f₀ : Perm (Fin 7) := swap 0 2 * (swap 4 6 * swap 5 6) * swap 1 3
  have hf_eq : τ * (swap (p 1) (p 3) * swap (p 5) (p 6) * τ *
        (swap (p 1) (p 3) * swap (p 5) (p 6))⁻¹) =
      swap (p 0) (p 2) * (swap (p 4) (p 6) * swap (p 5) (p 6)) * swap (p 1) (p 3) := by
    rw [show τ * (swap (p 1) (p 3) * swap (p 5) (p 6) * τ *
        (swap (p 1) (p 3) * swap (p 5) (p 6))⁻¹) =
        (τ * (swap (p 1) (p 3) * swap (p 5) (p 6)) * τ) *
        (swap (p 1) (p 3) * swap (p 5) (p 6))⁻¹ by group]
    rw [hconj, hσinv]
    group
  have hf_via : τ * (swap (p 1) (p 3) * swap (p 5) (p 6) * τ *
        (swap (p 1) (p 3) * swap (p 5) (p 6))⁻¹) =
      Equiv.Perm.viaEmbedding f₀ ⟨p, hp⟩ := by
    rw [hf_eq]
    apply Equiv.ext
    intro y
    by_cases hy : ∃ i, p i = y
    · obtain ⟨i, rfl⟩ := hy
      rw [show (f₀.viaEmbedding ⟨p, hp⟩) (p i) = p (f₀ i) from
        Equiv.Perm.viaEmbedding_apply f₀ ⟨p, hp⟩ i]
      fin_cases i <;>
        simp [f₀, Equiv.Perm.mul_apply, Equiv.swap_inv, Equiv.swap_apply_of_ne_of_ne, hp.ne_iff]
    · have hy' : y ∉ Set.range p := by simpa [Set.mem_range] using hy
      have hpy : ∀ i, y ≠ p i := fun i h => hy' ⟨i, h.symm⟩
      rw [Equiv.Perm.viaEmbedding_apply_of_notMem f₀ ⟨p, hp⟩ y hy']
      simp only [Equiv.Perm.mul_apply]
      rw [Equiv.swap_apply_of_ne_of_ne (hpy 1) (hpy 3),
        Equiv.swap_apply_of_ne_of_ne (hpy 5) (hpy 6),
        Equiv.swap_apply_of_ne_of_ne (hpy 4) (hpy 6),
        Equiv.swap_apply_of_ne_of_ne (hpy 0) (hpy 2)]
  refine ⟨swap (p 1) (p 3) * swap (p 5) (p 6), ?_⟩
  have hord : orderOf (τ * ((swap (p 1) (p 3) * swap (p 5) (p 6)) * τ *
        (swap (p 1) (p 3) * swap (p 5) (p 6))⁻¹)) = orderOf f₀ := by
    rw [hf_via]
    exact orderOf_injective (Equiv.Perm.viaEmbeddingHom ⟨p, hp⟩)
      (Equiv.Perm.viaEmbeddingHom_injective ⟨p, hp⟩) f₀
  rw [hord, orderOf_eq_iff (by norm_num : 0 < 6)]
  refine ⟨?_, ?_⟩
  · decide
  · intro m hm hpos
    interval_cases m <;> decide



theorem w85g_orderOf_six_free {α : Type} [DecidableEq α] {τ : Perm α} (hτ : τ * τ = 1)
    {p : Fin 10 → α} (hp : Function.Injective p)
    (hτp : ∀ i, τ (p i) = p ((swap 0 1 * swap 2 3 * swap 4 5 * swap 6 7 * swap 8 9 :
      Perm (Fin 10)) i)) :
    ∃ σ : Perm α, orderOf (τ * (σ * τ * σ⁻¹)) = 6 := by
  have idx : ∀ i j : Fin 10,
      (swap 0 1 * swap 2 3 * swap 4 5 * swap 6 7 * swap 8 9 : Perm (Fin 10)) i = j →
      τ (p i) = p j := by
    intro i j hij
    rw [← hij]
    exact hτp i
  have h1 : τ (p 1) = p 0 := idx 1 0 (by decide)
  have h3 : τ (p 3) = p 2 := idx 3 2 (by decide)
  have h5 : τ (p 5) = p 4 := idx 5 4 (by decide)
  have h6 : τ (p 6) = p 7 := idx 6 7 (by decide)
  have h7 : τ (p 7) = p 6 := idx 7 6 (by decide)
  have h8 : τ (p 8) = p 9 := idx 8 9 (by decide)
  have hconj1 : τ * swap (p 1) (p 3) * τ = swap (p 0) (p 2) := by
    rw [mul_swap_eq_swap_mul τ (p 1) (p 3), h1, h3,
      mul_assoc (swap (p 0) (p 2)) τ τ, hτ, mul_one]
  have hconj2 : τ * swap (p 5) (p 6) * τ = swap (p 4) (p 7) := by
    rw [mul_swap_eq_swap_mul τ (p 5) (p 6), h5, h6,
      mul_assoc (swap (p 4) (p 7)) τ τ, hτ, mul_one]
  have hconj3 : τ * swap (p 7) (p 8) * τ = swap (p 6) (p 9) := by
    rw [mul_swap_eq_swap_mul τ (p 7) (p 8), h7, h8,
      mul_assoc (swap (p 6) (p 9)) τ τ, hτ, mul_one]
  have hconj : τ * (swap (p 1) (p 3) * swap (p 5) (p 6) * swap (p 7) (p 8)) * τ =
      swap (p 0) (p 2) * swap (p 4) (p 7) * swap (p 6) (p 9) := by
    rw [show τ * (swap (p 1) (p 3) * swap (p 5) (p 6) * swap (p 7) (p 8)) * τ =
        (τ * swap (p 1) (p 3) * τ) * (τ * swap (p 5) (p 6) * τ) *
          (τ * swap (p 7) (p 8) * τ) by
      rw [show (τ * swap (p 1) (p 3) * τ) * (τ * swap (p 5) (p 6) * τ) *
          (τ * swap (p 7) (p 8) * τ) =
        τ * swap (p 1) (p 3) * (τ * τ) * swap (p 5) (p 6) * (τ * τ) *
          swap (p 7) (p 8) * τ by group]
      rw [hτ]
      group]
    rw [hconj1, hconj2, hconj3]
  have hσinv : (swap (p 1) (p 3) * swap (p 5) (p 6) * swap (p 7) (p 8) : Perm α)⁻¹ =
      swap (p 7) (p 8) * swap (p 5) (p 6) * swap (p 1) (p 3) := by
    rw [mul_inv_rev, mul_inv_rev, Equiv.swap_inv, Equiv.swap_inv, Equiv.swap_inv]
    group
  let f₀ : Perm (Fin 10) := swap 0 2 * swap 4 7 * swap 6 9 * swap 7 8 * swap 5 6 * swap 1 3
  have hf_eq : τ * (swap (p 1) (p 3) * swap (p 5) (p 6) * swap (p 7) (p 8) * τ *
        (swap (p 1) (p 3) * swap (p 5) (p 6) * swap (p 7) (p 8))⁻¹) =
      swap (p 0) (p 2) * swap (p 4) (p 7) * swap (p 6) (p 9) * swap (p 7) (p 8) *
        swap (p 5) (p 6) * swap (p 1) (p 3) := by
    rw [show τ * (swap (p 1) (p 3) * swap (p 5) (p 6) * swap (p 7) (p 8) * τ *
        (swap (p 1) (p 3) * swap (p 5) (p 6) * swap (p 7) (p 8))⁻¹) =
        (τ * (swap (p 1) (p 3) * swap (p 5) (p 6) * swap (p 7) (p 8)) * τ) *
        (swap (p 1) (p 3) * swap (p 5) (p 6) * swap (p 7) (p 8))⁻¹ by group]
    rw [hconj, hσinv]
    group
  have hf_via : τ * (swap (p 1) (p 3) * swap (p 5) (p 6) * swap (p 7) (p 8) * τ *
        (swap (p 1) (p 3) * swap (p 5) (p 6) * swap (p 7) (p 8))⁻¹) =
      Equiv.Perm.viaEmbedding f₀ ⟨p, hp⟩ := by
    rw [hf_eq]
    apply Equiv.ext
    intro y
    by_cases hy : ∃ i, p i = y
    · obtain ⟨i, rfl⟩ := hy
      rw [show (f₀.viaEmbedding ⟨p, hp⟩) (p i) = p (f₀ i) from
        Equiv.Perm.viaEmbedding_apply f₀ ⟨p, hp⟩ i]
      fin_cases i <;>
        simp [f₀, Equiv.Perm.mul_apply, Equiv.swap_inv, Equiv.swap_apply_of_ne_of_ne, hp.ne_iff]
    · have hy' : y ∉ Set.range p := by simpa [Set.mem_range] using hy
      have hpy : ∀ i, y ≠ p i := fun i h => hy' ⟨i, h.symm⟩
      rw [Equiv.Perm.viaEmbedding_apply_of_notMem f₀ ⟨p, hp⟩ y hy']
      simp only [Equiv.Perm.mul_apply]
      rw [Equiv.swap_apply_of_ne_of_ne (hpy 1) (hpy 3),
        Equiv.swap_apply_of_ne_of_ne (hpy 5) (hpy 6),
        Equiv.swap_apply_of_ne_of_ne (hpy 7) (hpy 8),
        Equiv.swap_apply_of_ne_of_ne (hpy 6) (hpy 9),
        Equiv.swap_apply_of_ne_of_ne (hpy 4) (hpy 7),
        Equiv.swap_apply_of_ne_of_ne (hpy 0) (hpy 2)]
  refine ⟨swap (p 1) (p 3) * swap (p 5) (p 6) * swap (p 7) (p 8), ?_⟩
  have hord : orderOf (τ * ((swap (p 1) (p 3) * swap (p 5) (p 6) * swap (p 7) (p 8)) * τ *
        (swap (p 1) (p 3) * swap (p 5) (p 6) * swap (p 7) (p 8))⁻¹)) = orderOf f₀ := by
    rw [hf_via]
    exact orderOf_injective (Equiv.Perm.viaEmbeddingHom ⟨p, hp⟩)
      (Equiv.Perm.viaEmbeddingHom_injective ⟨p, hp⟩) f₀
  rw [hord]
  exact w85g_orderOf_eq_six_of_pow (by decide +kernel) (by decide +kernel) (by decide +kernel)

end CFSG.LocalAnalysis.WeakClosure81

end
