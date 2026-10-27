module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35Fin10

public section

namespace CFSG.Quasithin.F53.Stellmacher.S35.Fin

open Equiv CFSG.Quasithin CFSG.Quasithin.F53Mod

theorem not_isSwap_mul {x y : Perm (Fin 5)} (hx : x.IsSwap) (hy : y.IsSwap) :
    ¬ (x * y).IsSwap := by
  intro h
  have h1 := (isSwap_iff_mul_self.mp h).2.2
  have h2 := (isSwap_iff_mul_self.mp hx).2.2
  have h3 := (isSwap_iff_mul_self.mp hy).2.2
  rw [Perm.sign_mul] at h1
  rcases Int.units_eq_one_or (Perm.sign x) with e | e
  · exact h2 e
  rcases Int.units_eq_one_or (Perm.sign y) with e' | e'
  · exact h3 e'
  rw [e, e'] at h1
  exact h1 (by decide)

theorem swap_or_mul_swap {A : Subgroup (Perm (Fin 5))} (hA : IsElemAb A) (hq : IsQuad A)
    {s g : Perm (Fin 5)} (hs : s ∈ A) (hsw : s.IsSwap) (hg : g ∈ A) (hg1 : g ≠ 1) :
    g.IsSwap ∨ (g * s).IsSwap := by
  rcases (isQuad_elemAb_iff hA).mp hq with h | ⟨x, hx1, hxx, hAx⟩ | ⟨s', t', hne, hc, hs', ht', hA'⟩
  · rw [h] at hg
    exact absurd (Subgroup.mem_bot.mp hg) hg1
  · left
    rw [hAx] at hs hg
    have hsx : s = x := ((mem_zpowers_iff_of_mul_self hxx).mp hs).resolve_left
      (isSwap_iff_mul_self.mp hsw).1
    have hgx : g = x := ((mem_zpowers_iff_of_mul_self hxx).mp hg).resolve_left hg1
    rw [hgx, ← hsx]
    exact hsw
  · have hss' : s' * s' = 1 := (isSwap_iff_mul_self.mp hs').2.1
    have htt' : t' * t' = 1 := (isSwap_iff_mul_self.mp ht').2.1
    rw [hA', mem_closure_pair hss' htt' hc] at hs hg
    simp only [kl, Finset.mem_insert, Finset.mem_singleton] at hs hg
    have hs1 : s ≠ 1 := (isSwap_iff_mul_self.mp hsw).1
    have hst : s = s' ∨ s = t' := by
      rcases hs with h | h | h | h
      · exact absurd h hs1
      · exact Or.inl h
      · exact Or.inr h
      · exact absurd (h ▸ hsw) (not_isSwap_mul hs' ht')
    rcases hg with h | h | h | h
    · exact absurd h hg1
    · exact Or.inl (h ▸ hs')
    · exact Or.inl (h ▸ ht')
    · right
      rcases hst with e | e
      · rw [e]
        have : g * s' = t' := by
          rw [h, mul_assoc, ← hc, ← mul_assoc, hss', one_mul]
        rw [this]; exact ht'
      · rw [e]
        have : g * t' = s' := by
          rw [h, mul_assoc, htt', mul_one]
        rw [this]; exact hs'

end CFSG.Quasithin.F53.Stellmacher.S35.Fin
