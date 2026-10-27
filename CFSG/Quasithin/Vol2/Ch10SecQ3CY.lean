module

public import Mathlib.GroupTheory.Perm.Support
public import Mathlib.Data.Fintype.Perm
public import Mathlib.Data.ZMod.QuotientGroup
public import Mathlib.Tactic.Group

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecB

namespace C11AmS

open Equiv

theorem fix_of_comm_swap {α : Type*} [DecidableEq α] [Finite α] {σ : Perm α} {a b : α}
    (hab : a ≠ b) (hc : σ * swap a b = swap a b * σ) (ho : Odd (orderOf σ)) : σ a = a := by
  have h1 : swap (σ a) (σ b) = swap a b := by
    have := mul_swap_eq_swap_mul σ a b
    rw [hc] at this
    exact (mul_right_cancel this).symm
  have h2 : swap a b (σ a) = σ b := by rw [← h1, swap_apply_left]
  have hσab : σ a ≠ σ b := fun h => hab (σ.injective h)
  have h3 : σ a = a ∨ σ a = b := by
    by_contra hne
    push Not at hne
    rw [swap_apply_of_ne_of_ne hne.1 hne.2] at h2
    exact hσab h2
  rcases h3 with h | h
  · exact h
  · exfalso
    have h4 : σ b = a := by rw [← h2, h, swap_apply_right]
    have h5 : (σ ^ 2) a = a := by rw [pow_two, Perm.mul_apply, h, h4]
    have h6 : ∀ j : ℕ, (σ ^ (2 * j)) a = a := by
      intro j
      induction j with
      | zero => simp
      | succ j ih => rw [mul_add, mul_one, pow_add, Perm.mul_apply, h5, ih]
    obtain ⟨j, hj⟩ := ho
    have h7 : (σ ^ orderOf σ) a = a := by rw [pow_orderOf_eq_one, Perm.one_apply]
    rw [hj, pow_succ', Perm.mul_apply, h6 j, h] at h7
    exact hab h7.symm

theorem not_six_distinct {x y a b c d : Fin 5} (hxy : x ≠ y) (hxa : x ≠ a) (hxb : x ≠ b)
    (hxc : x ≠ c) (hxd : x ≠ d) (hya : y ≠ a) (hyb : y ≠ b) (hyc : y ≠ c) (hyd : y ≠ d)
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) :
    False := by
  classical
  have h : ({x, y, a, b, c, d} : Finset (Fin 5)).card = 6 := by
    rw [Finset.card_insert_of_notMem (by simp [hxy, hxa, hxb, hxc, hxd]),
      Finset.card_insert_of_notMem (by simp [hya, hyb, hyc, hyd]),
      Finset.card_insert_of_notMem (by simp [hab, hac, had]),
      Finset.card_insert_of_notMem (by simp [hbc, hbd]), Finset.card_pair hcd]
  have h1 := Finset.card_le_univ ({x, y, a, b, c, d} : Finset (Fin 5))
  rw [h, Fintype.card_fin] at h1
  omega

theorem eq_one_of_comm_swaps {σ : Perm (Fin 5)} {a b c d : Fin 5} (hab : a ≠ b) (hcd : c ≠ d)
    (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d)
    (h1 : σ * swap a b = swap a b * σ) (h2 : σ * swap c d = swap c d * σ)
    (ho : Odd (orderOf σ)) : σ = 1 := by
  have ha := fix_of_comm_swap hab h1 ho
  have hb := fix_of_comm_swap hab.symm (by rw [swap_comm]; exact h1) ho
  have hc := fix_of_comm_swap hcd h2 ho
  have hd := fix_of_comm_swap hcd.symm (by rw [swap_comm]; exact h2) ho
  refine Equiv.ext fun x => ?_
  rw [Perm.one_apply]
  by_contra hx
  have hxa : x ≠ a := fun h => hx (h ▸ ha)
  have hxb : x ≠ b := fun h => hx (h ▸ hb)
  have hxc : x ≠ c := fun h => hx (h ▸ hc)
  have hxd : x ≠ d := fun h => hx (h ▸ hd)
  have hya : σ x ≠ a := fun h => hxa (σ.injective (h.trans ha.symm))
  have hyb : σ x ≠ b := fun h => hxb (σ.injective (h.trans hb.symm))
  have hyc : σ x ≠ c := fun h => hxc (σ.injective (h.trans hc.symm))
  have hyd : σ x ≠ d := fun h => hxd (σ.injective (h.trans hd.symm))
  exact not_six_distinct (Ne.symm hx) hxa hxb hxc hxd hya hyb hyc hyd hab hac had hbc hbd hcd

theorem swaps_noncomm : ∀ a b c d : Fin 5, a ≠ b → c ≠ d →
    swap a b * swap c d ≠ swap c d * swap a b → (swap a b * swap c d) ^ 3 = 1 := by decide

theorem swaps_comm_disj : ∀ a b c d : Fin 5, a ≠ b → c ≠ d → swap a b ≠ swap c d →
    swap a b * swap c d = swap c d * swap a b → a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d := by decide

theorem not_isSwap_mul {a b c d : Fin 5} (hab : a ≠ b) (hcd : c ≠ d) (hac : a ≠ c)
    (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) : ¬ (swap a b * swap c d).IsSwap := by
  rintro ⟨x, y, hxy, h⟩
  have hmoves : ∀ z, (swap a b * swap c d) z ≠ z → z = x ∨ z = y := by
    intro z hz
    by_contra hne
    push Not at hne
    exact hz (by rw [h, swap_apply_of_ne_of_ne hne.1 hne.2])
  have ha := hmoves a (by
    rw [Perm.mul_apply, swap_apply_of_ne_of_ne hac had, swap_apply_left]; exact hab.symm)
  have hb := hmoves b (by
    rw [Perm.mul_apply, swap_apply_of_ne_of_ne hbc hbd, swap_apply_right]; exact hab)
  have hc := hmoves c (by
    rw [Perm.mul_apply, swap_apply_left, swap_apply_of_ne_of_ne (Ne.symm had) (Ne.symm hbd)]
    exact hcd.symm)
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> rcases hc with rfl | rfl <;>
    simp_all

theorem eq_one_of_normalizes_swaps {Q : Subgroup (Perm (Fin 5))} {A : Set (Perm (Fin 5))}
    (hA : ∀ x ∈ A, x.IsSwap) (hQ : Q = Subgroup.closure A) (hcard : Nat.card Q = 4)
    {σ : Perm (Fin 5)} (hσ : ∀ x ∈ Q, σ * x * σ⁻¹ ∈ Q) (ho : Odd (orderOf σ)) : σ = 1 := by
  classical
  have hAQ : A ⊆ Q := hQ ▸ Subgroup.subset_closure
  obtain ⟨τ₁, hτ₁⟩ : A.Nonempty := by
    by_contra h
    rw [Set.not_nonempty_iff_eq_empty] at h
    rw [hQ, h, Subgroup.closure_empty, Subgroup.card_bot] at hcard
    omega
  obtain ⟨τ₂, hτ₂, hne⟩ : ∃ τ₂ ∈ A, τ₂ ≠ τ₁ := by
    by_contra h
    push Not at h
    have hle : Q ≤ Subgroup.zpowers τ₁ := by
      rw [hQ, Subgroup.closure_le]
      intro x hx
      rw [h x hx]
      exact Subgroup.mem_zpowers τ₁
    have h1 := Subgroup.card_le_of_le hle
    obtain ⟨a, b, hab, rfl⟩ := hA τ₁ hτ₁
    have hne1 : swap a b ≠ 1 := fun h => hab (by
      have := congrArg (fun f : Perm (Fin 5) => f a) h
      simpa using this.symm)
    rw [hcard, Nat.card_zpowers, orderOf_eq_prime (by rw [pow_two, swap_mul_self]) hne1] at h1
    omega
  obtain ⟨a, b, hab, rfl⟩ := hA _ hτ₁
  obtain ⟨c, d, hcd, rfl⟩ := hA _ hτ₂
  have hcomm : swap a b * swap c d = swap c d * swap a b := by
    by_contra hnc
    have h3 := swaps_noncomm a b c d hab hcd hnc
    have h1 : swap a b * swap c d ≠ 1 := fun h => hne (by
      rw [mul_eq_one_iff_eq_inv, swap_inv] at h
      exact h.symm)
    have ho3 := orderOf_eq_prime h3 h1
    have hdvd := Subgroup.orderOf_dvd_natCard Q (Q.mul_mem (hAQ hτ₁) (hAQ hτ₂))
    rw [ho3, hcard] at hdvd
    omega
  obtain ⟨hac, had, hbc, hbd⟩ := swaps_comm_disj a b c d hab hcd hne.symm hcomm
  have h1 : swap a b ∈ Q := hAQ hτ₁
  have h2 : swap c d ∈ Q := hAQ hτ₂
  have hne1 : ∀ {u v : Fin 5}, u ≠ v → swap u v ≠ 1 := fun {u v} huv h => huv (by
    have := congrArg (fun f : Perm (Fin 5) => f u) h
    simpa using this.symm)
  have hswapQ : ∀ x ∈ Q, x.IsSwap → x = swap a b ∨ x = swap c d := by
    intro x hx hsx
    by_contra hcon
    push Not at hcon
    have h3 : swap a b * swap c d ∈ Q := Q.mul_mem h1 h2
    obtain ⟨u, v, huv, rfl⟩ := hsx
    have hm1 : swap a b * swap c d ≠ swap a b := fun h => hne1 hcd (by
      simpa using h)
    have hm2 : swap a b * swap c d ≠ swap c d := fun h => hne1 hab (by
      rw [mul_eq_right] at h
      exact h)
    have hm3 : swap a b * swap c d ≠ 1 := fun h => hne (by
      rw [mul_eq_one_iff_eq_inv, swap_inv] at h
      exact h.symm)
    have hm4 : swap a b * swap c d ≠ swap u v := fun h =>
      not_isSwap_mul hab hcd hac had hbc hbd ⟨u, v, huv, h⟩
    have hsub : ({1, swap a b, swap c d, swap a b * swap c d, swap u v} : Finset (Perm (Fin 5)))
        ⊆ (Q : Set (Perm (Fin 5))).toFinset := by
      intro y hy
      simp only [Finset.mem_insert, Finset.mem_singleton] at hy
      rw [Set.mem_toFinset]
      rcases hy with rfl | rfl | rfl | rfl | rfl
      exacts [Q.one_mem, h1, h2, h3, hx]
    have hcard5 : ({1, swap a b, swap c d, swap a b * swap c d, swap u v} :
        Finset (Perm (Fin 5))).card = 5 := by
      rw [Finset.card_insert_of_notMem (by
          simp [Ne.symm (hne1 hab), Ne.symm (hne1 hcd), Ne.symm hm3, Ne.symm (hne1 huv)]),
        Finset.card_insert_of_notMem (by simp [hne.symm, Ne.symm hm1, hcon.1.symm]),
        Finset.card_insert_of_notMem (by simp [Ne.symm hm2, hcon.2.symm]), Finset.card_pair hm4]
    have h4 := Finset.card_le_card hsub
    have h5 : Fintype.card ↑(Q : Set (Perm (Fin 5))) = 4 := by
      rw [← Nat.card_eq_fintype_card]
      exact hcard
    rw [hcard5, Set.toFinset_card, h5] at h4
    omega
  have hf : ∀ x ∈ Q, x.IsSwap → σ * x * σ⁻¹ = swap a b ∨ σ * x * σ⁻¹ = swap c d := by
    rintro x hx ⟨u, v, huv, rfl⟩
    refine hswapQ _ (hσ _ hx) ⟨σ u, σ v, fun h => huv (σ.injective h), ?_⟩
    rw [swap_apply_apply]
  have key : ∀ y z : Perm (Fin 5), y ≠ z → (σ * y * σ⁻¹ = y ∨ σ * y * σ⁻¹ = z) →
      (σ * z * σ⁻¹ = y ∨ σ * z * σ⁻¹ = z) → σ ^ 2 * y = y * σ ^ 2 := by
    intro y z hyz hy hz
    have e : σ ^ 2 * y * (σ ^ 2)⁻¹ = σ * (σ * y * σ⁻¹) * σ⁻¹ := by
      rw [pow_two, mul_inv_rev]
      group
    have e2 : σ ^ 2 * y * (σ ^ 2)⁻¹ = y := by
      rcases hy with h | h
      · rw [e, h, h]
      · rw [e, h]
        rcases hz with h' | h'
        · exact h'
        · exfalso
          apply hyz
          have := h.trans h'.symm
          simpa using this
    calc σ ^ 2 * y = σ ^ 2 * y * (σ ^ 2)⁻¹ * σ ^ 2 := by rw [inv_mul_cancel_right]
      _ = y * σ ^ 2 := by rw [e2]
  have hsab := key (swap a b) (swap c d) hne.symm (hf _ h1 ⟨a, b, hab, rfl⟩)
    (hf _ h2 ⟨c, d, hcd, rfl⟩)
  have hscd := key (swap c d) (swap a b) hne ((hf _ h2 ⟨c, d, hcd, rfl⟩).symm)
    ((hf _ h1 ⟨a, b, hab, rfl⟩).symm)
  have ho2 : Odd (orderOf (σ ^ 2)) := ho.of_dvd_nat (orderOf_pow_dvd 2)
  have hσ2 := eq_one_of_comm_swaps hab hcd hac had hbc hbd hsab hscd ho2
  have h5 : orderOf σ ∣ 2 := orderOf_dvd_of_pow_eq_one hσ2
  rcases (Nat.dvd_prime Nat.prime_two).mp h5 with h | h
  · exact orderOf_eq_one_iff.mp h
  · rw [h] at ho
    exact absurd ho (by decide)

end C11AmS

end CFSG.Quasithin.Vol2.Ch10.SecB
