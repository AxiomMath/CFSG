module

public import CFSG.Permutation.FiveTransitive.ThreeSwapTwoGroup

public section

namespace CFSG

namespace FiveTransitive.ThreeSwapMove

open Equiv MulAction

theorem apply_eq_or_eq {F : Type*} [DecidableEq F]
    (v : Perm F) (a b : F) (hab : a ≠ b) (hc : Commute v (swap a b)) :
    v a = a ∨ v a = b := by
  by_contra hn
  have hna : v a ≠ a := fun h => hn (Or.inl h)
  have hnb : v a ≠ b := fun h => hn (Or.inr h)
  have he := DFunLike.congr_fun hc.eq a
  simp only [Perm.mul_apply, swap_apply_left, swap_apply_of_ne_of_ne hna hnb] at he
  exact hab (v.injective he).symm

theorem swap_image_mem {F : Type*} [DecidableEq F]
    (e : Fin 6 ↪ F) (v : Perm F) (hv : v ∈ ThreeSwapTwoGroup.subgroup e) (a : F) :
    swap a (v a) ∈ ThreeSwapTwoGroup.subgroup e := by
  classical
  let S : Set (Perm F) := {swap (e 0) (e 1), swap (e 2) (e 3), swap (e 4) (e 5)}
  let V := ThreeSwapTwoGroup.subgroup e
  by_cases hmove : v a = a
  · rw [hmove, swap_self]
    exact V.one_mem
  have hex : ∃ t ∈ S, t a ≠ a := by
    by_contra hn
    have hfix : V ≤ stabilizer (Perm F) a := by
      apply (Subgroup.closure_le _).mpr
      intro t ht
      change t a = a
      by_contra hm
      exact hn ⟨t, ht, hm⟩
    exact hmove (hfix hv)
  obtain ⟨t, ht, hta⟩ := hex
  have htV : t ∈ V := Subgroup.subset_closure ht
  have htSwap : t.IsSwap := by
    simp only [S, Set.mem_insert_iff, Set.mem_singleton_iff] at ht
    rcases ht with rfl | rfl | rfl
    · exact ⟨e 0, e 1, e.injective.ne (by decide), rfl⟩
    · exact ⟨e 2, e 3, e.injective.ne (by decide), rfl⟩
    · exact ⟨e 4, e 5, e.injective.ne (by decide), rfl⟩
  have hinv (w : V) : w⁻¹ = w := inv_eq_of_mul_eq_one_right (by
    simpa only [pow_two] using (ThreeSwapTwoGroup.isTwoGroup e).2 w)
  have hc : Commute v t := by
    have he : (⟨v, hv⟩ : V) * ⟨t, htV⟩ = (⟨t, htV⟩ : V) * ⟨v, hv⟩ := by
      calc
        _ = ((⟨v, hv⟩ : V) * ⟨t, htV⟩)⁻¹ := (hinv _).symm
        _ = _ := by rw [mul_inv_rev, hinv, hinv]
    exact congrArg Subtype.val he
  obtain ⟨b, c, hbc, rfl⟩ := htSwap
  have ha : a = b ∨ a = c := by
    by_contra hn
    exact hta (swap_apply_of_ne_of_ne (fun h => hn (Or.inl h)) (fun h => hn (Or.inr h)))
  rcases ha with ha | ha
  · subst a
    have he : v b = c := (apply_eq_or_eq v b c hbc hc).resolve_left hmove
    simpa only [he] using htV
  · subst a
    have hc' : Commute v (swap c b) := by simpa only [swap_comm] using hc
    have he : v c = b := (apply_eq_or_eq v c b hbc.symm hc').resolve_left hmove
    simpa only [he, swap_comm] using htV

end FiveTransitive.ThreeSwapMove

end CFSG
