module

public import Mathlib.GroupTheory.Perm.Cycle.Type
public import Mathlib.Data.Nat.Totient

public section

namespace CFSG.RankThree.PartOne.LyFive

open Equiv Equiv.Perm

theorem fix_support_of_commute_cycle {α : Type*} [Fintype α] [DecidableEq α] {c σ : Perm α}
    (hc : c.IsCycle) (hc5 : orderOf c = 5) (hσ : σ * σ = 1) (hcom : Commute σ c) {x : α}
    (hx : c x ≠ x) : σ x = x := by
  have hsx : σ x ∈ c.support := (mem_support_iff_of_commute hcom x).2 (mem_support.2 hx)
  have hcy : c.SameCycle x (σ x) := hc.sameCycle hx (mem_support.1 hsx)
  obtain ⟨i, -, -, hi⟩ := SameCycle.exists_pow_eq c hcy
  have h1 : σ (σ x) = x := by simpa using congrArg (fun p : Perm α => p x) hσ
  have h2 : σ ((c ^ i) x) = (c ^ i) (σ x) := by
    have := congrArg (fun p : Perm α => p x) (hcom.pow_right i).eq
    simpa using this
  have h3 : (c ^ (i + i)) x = x := by
    rw [pow_add, Perm.mul_apply, hi, ← h2, hi, h1]
  have h4 : c ^ (i + i) = 1 := (hc.pow_eq_one_iff' hx).2 h3
  have h5 : 5 ∣ i + i := hc5 ▸ orderOf_dvd_of_pow_eq_one h4
  have h6 : c ^ i = 1 := by
    rw [← orderOf_dvd_iff_pow_eq_one, hc5]
    omega
  rw [← hi, h6]
  rfl

theorem eq_one_of_commute_even_centralizer (w σ : Perm (Fin 11)) (hw5 : w ^ 5 = 1)
    (hσ : σ * σ = 1)
    (hcomm : ∀ g : Perm (Fin 11), sign g = 1 → Commute g w → Commute g σ) : σ = 1 := by
  classical
  by_contra hne
  have hfix : ∀ x, w x ≠ x → σ x = x := by
    intro x hx
    have hcyc : (w.cycleOf x).IsCycle := isCycle_cycleOf w hx
    have hcF : w.cycleOf x ∈ w.cycleFactorsFinset :=
      cycleOf_mem_cycleFactorsFinset_iff.2 (mem_support.2 hx)
    have hcw : Commute (w.cycleOf x) w := self_mem_cycle_factors_commute hcF
    have hxc : (w.cycleOf x) x ≠ x := by rw [cycleOf_apply_self]; exact hx
    have hord : orderOf (w.cycleOf x) ∣ 5 :=
      (orderOf_cycleOf_dvd_orderOf w x).trans (orderOf_dvd_of_pow_eq_one hw5)
    have hne1 : orderOf (w.cycleOf x) ≠ 1 := by
      intro h
      rw [orderOf_eq_one_iff] at h
      exact hxc (by rw [h]; rfl)
    have h5 : orderOf (w.cycleOf x) = 5 :=
      ((Nat.dvd_prime Nat.prime_five).1 hord).resolve_left hne1
    have hsgn : sign (w.cycleOf x) = 1 := by
      rw [hcyc.sign, ← hcyc.orderOf, h5]
      decide
    exact fix_support_of_commute_cycle hcyc h5 hσ (hcomm _ hsgn hcw).symm hxc
  have hex : ∃ i, σ i ≠ i := by
    by_contra h
    simp only [not_exists, not_not] at h
    exact hne (Equiv.ext h)
  obtain ⟨i, hi⟩ := hex
  have hσσ : ∀ x, σ (σ x) = x := fun x => by simpa using congrArg (fun p : Perm (Fin 11) => p x) hσ
  have hwi : w i = i := by
    by_contra h
    exact hi (hfix i h)
  have hwj : w (σ i) = σ i := by
    by_contra h
    have h1 := hfix _ h
    rw [hσσ] at h1
    exact hi h1.symm
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have hF : (w.supportᶜ).card ≡ Fintype.card (Fin 11) [MOD 5] :=
    card_compl_support_modEq (p := 5) (n := 1) (by simpa using hw5)
  have hiF : i ∈ w.supportᶜ := Finset.mem_compl.2 (notMem_support.2 hwi)
  have hjF : σ i ∈ w.supportᶜ := Finset.mem_compl.2 (notMem_support.2 hwj)
  have hFle : (w.supportᶜ).card ≤ 11 := by
    simpa using Finset.card_le_univ (w.supportᶜ)
  have hF2 : 2 ≤ (w.supportᶜ).card := by
    have : ({i, σ i} : Finset (Fin 11)) ⊆ w.supportᶜ := by
      intro x hx
      rcases Finset.mem_insert.1 hx with rfl | hx
      · exact hiF
      · rw [Finset.mem_singleton.1 hx]; exact hjF
    have h2 : ({i, σ i} : Finset (Fin 11)).card = 2 := Finset.card_pair (Ne.symm hi)
    rw [← h2]
    exact Finset.card_le_card this
  have hF6 : 6 ≤ (w.supportᶜ).card := by
    unfold Nat.ModEq at hF
    simp only [Fintype.card_fin] at hF
    omega
  set G : Finset (Fin 11) := ((w.supportᶜ).erase i).erase (σ i) with hG
  have hGcard : 4 ≤ G.card := by
    have e1 : ((w.supportᶜ).erase i).card = (w.supportᶜ).card - 1 :=
      Finset.card_erase_of_mem hiF
    have e2 : G.card = ((w.supportᶜ).erase i).card - 1 :=
      Finset.card_erase_of_mem (Finset.mem_erase.2 ⟨hi, hjF⟩)
    omega
  obtain ⟨k, hkG, l, hlG, hkl⟩ := Finset.one_lt_card.1 (by omega : 1 < G.card)
  have hk := Finset.mem_erase.1 hkG
  have hl := Finset.mem_erase.1 hlG
  have hk' := Finset.mem_erase.1 hk.2
  have hl' := Finset.mem_erase.1 hl.2
  have hik : i ≠ k := fun h => hk'.1 h.symm
  have hil : i ≠ l := fun h => hl'.1 h.symm
  have hnd : [i, k, l].Nodup := by simp [hik, hil, hkl]
  set τ : Perm (Fin 11) := swap i k * swap k l with hτ
  have hτs : τ.support = {i, k, l} := support_swap_mul_swap hnd
  have hsign : sign τ = 1 := by
    simp [hτ, sign_mul, sign_swap hik, sign_swap hkl]
  have hdisj : τ.Disjoint w := fun x => by
    by_cases hx : x ∈ τ.support
    · right
      rw [hτs] at hx
      have hxF : x ∈ w.supportᶜ := by
        rcases Finset.mem_insert.1 hx with rfl | hx
        · exact hiF
        · rcases Finset.mem_insert.1 hx with rfl | hx
          · exact hk'.2
          · rw [Finset.mem_singleton.1 hx]; exact hl'.2
      exact notMem_support.1 (Finset.mem_compl.1 hxF)
    · left
      exact notMem_support.1 hx
  have hcτ : Commute τ σ := hcomm τ hsign hdisj.commute
  have hconj : σ * τ * σ⁻¹ = τ := by
    rw [← hcτ.eq, mul_assoc, mul_inv_cancel, mul_one]
  have hsupp := support_conj (σ := σ) (τ := τ)
  rw [hconj, hτs] at hsupp
  have hmem : σ i ∈ ({i, k, l} : Finset (Fin 11)) := by
    rw [hsupp]
    exact Finset.mem_map.2 ⟨i, by simp, rfl⟩
  rcases Finset.mem_insert.1 hmem with h | h
  · exact hi h
  · rcases Finset.mem_insert.1 h with h | h
    · exact hk.1 h.symm
    · exact hl.1 (Finset.mem_singleton.1 h).symm

end CFSG.RankThree.PartOne.LyFive
