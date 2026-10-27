module

public import Mathlib.GroupTheory.Perm.Sign
public import Mathlib.Algebra.Group.Subgroup.Ker
public import Mathlib.Tactic.Group

public section

namespace CFSG.StandardType

open Equiv

theorem share_of_not_commute_swap {α : Type*} [DecidableEq α] {x y u v : α}
    (h : swap x y * swap u v ≠ swap u v * swap x y) : x = u ∨ x = v ∨ y = u ∨ y = v := by
  by_contra hne
  push Not at hne
  obtain ⟨hxu, hxv, hyu, hyv⟩ := hne
  by_cases hxy : x = y
  · rw [hxy, swap_self] at h
    exact h rfl
  by_cases huv : u = v
  · rw [huv, swap_self] at h
    exact h rfl
  exact h (Perm.Disjoint.commute (Perm.disjoint_swap_swap (by simp [hxy, hxu, hxv, hyu, hyv, huv])))

theorem exists_eq_conj_of_isSwap {d : ℕ} (hd : 3 ≤ d) (f : Perm (Fin d) →* Perm (Fin d))
    (hinj : Function.Injective f) (hswap : ∀ σ : Perm (Fin d), σ.IsSwap → (f σ).IsSwap) :
    ∃ π : Perm (Fin d), ∀ σ, f σ = π * σ * π⁻¹ := by
  classical
  obtain ⟨o, k₁, k₂, ho1, ho2, h12⟩ : ∃ o k₁ k₂ : Fin d, o ≠ k₁ ∧ o ≠ k₂ ∧ k₁ ≠ k₂ :=
    ⟨⟨0, by omega⟩, ⟨1, by omega⟩, ⟨2, by omega⟩, by simp [Fin.ext_iff], by simp [Fin.ext_iff],
      by simp [Fin.ext_iff]⟩
  have hev : ∀ k k' : Fin d, k ≠ o → swap o k = swap o k' → k = k' := by
    intro k k' hk h
    have h1 := congrArg (fun σ : Perm (Fin d) => σ o) h
    simpa only [swap_apply_left] using h1
  have hnc : ∀ k k' : Fin d, k ≠ o → k' ≠ o → k ≠ k' →
      swap o k * swap o k' ≠ swap o k' * swap o k := by
    intro k k' hk hk' hkk' h
    have h1 := congrArg (fun σ : Perm (Fin d) => σ o) h
    simp only [Perm.mul_apply, swap_apply_left] at h1
    rw [swap_apply_of_ne_of_ne hk' (Ne.symm hkk'), swap_apply_of_ne_of_ne hk hkk'] at h1
    exact hkk' h1.symm
  have hfnc : ∀ k k' : Fin d, k ≠ o → k' ≠ o → k ≠ k' →
      f (swap o k) * f (swap o k') ≠ f (swap o k') * f (swap o k) := by
    intro k k' hk hk' hkk' h
    rw [← map_mul, ← map_mul] at h
    exact hnc k k' hk hk' hkk' (hinj h)
  have hfne : ∀ k k' : Fin d, k ≠ o → k ≠ k' → f (swap o k) ≠ f (swap o k') :=
    fun k k' hk hkk' h => hkk' (hev k k' hk (hinj h))
  have hsk : ∀ k : Fin d, k ≠ o → ∃ x y, x ≠ y ∧ f (swap o k) = swap x y := fun k hk =>
    hswap _ ⟨o, k, Ne.symm hk, rfl⟩
  obtain ⟨a, b, c, hab, hac, hbc, hfa, hfb⟩ : ∃ a b c : Fin d, a ≠ b ∧ a ≠ c ∧ b ≠ c ∧
      f (swap o k₁) = swap a b ∧ f (swap o k₂) = swap a c := by
    obtain ⟨x₁, y₁, hxy₁, h₁⟩ := hsk k₁ (Ne.symm ho1)
    obtain ⟨x₂, y₂, hxy₂, h₂⟩ := hsk k₂ (Ne.symm ho2)
    have hnc12 := hfnc k₁ k₂ (Ne.symm ho1) (Ne.symm ho2) h12
    have hne12 := hfne k₁ k₂ (Ne.symm ho1) h12
    rw [h₁, h₂] at hnc12 hne12
    rcases share_of_not_commute_swap hnc12 with h | h | h | h
    · exact ⟨x₁, y₁, y₂, hxy₁, h ▸ hxy₂, fun hyy => hne12 (by rw [h, hyy]), h₁, by rw [h₂, h]⟩
    · exact ⟨x₁, y₁, x₂, hxy₁, h ▸ hxy₂.symm, fun hyx => hne12 (by rw [h, hyx, swap_comm]), h₁,
        by rw [h₂, h, swap_comm]⟩
    · exact ⟨y₁, x₁, y₂, hxy₁.symm, h ▸ hxy₂, fun hxy => hne12 (by rw [hxy, h, swap_comm]),
        by rw [h₁, swap_comm], by rw [h₂, h]⟩
    · exact ⟨y₁, x₁, x₂, hxy₁.symm, h ▸ hxy₂.symm, fun hxx => hne12 (by rw [hxx, h]),
        by rw [h₁, swap_comm], by rw [h₂, h, swap_comm]⟩
  have hfbc : f (swap k₁ k₂) = swap b c := by
    have e1 : swap k₁ k₂ = swap o k₁ * swap o k₂ * swap o k₁ := by
      have h1 := swap_apply_apply (swap o k₁) o k₂
      rwa [swap_apply_left, swap_apply_of_ne_of_ne (Ne.symm ho2) (Ne.symm h12), swap_inv] at h1
    have e2 : swap b c = swap a b * swap a c * swap a b := by
      have h1 := swap_apply_apply (swap a b) a c
      rwa [swap_apply_left, swap_apply_of_ne_of_ne (Ne.symm hac) (Ne.symm hbc), swap_inv] at h1
    rw [e1, map_mul, map_mul, hfa, hfb, e2]
  have hstar : ∀ k : Fin d, k ≠ o → ∃ x, x ≠ a ∧ f (swap o k) = swap a x := by
    intro k hk
    by_cases hk1 : k = k₁
    · exact ⟨b, Ne.symm hab, by rw [hk1, hfa]⟩
    by_cases hk2 : k = k₂
    · exact ⟨c, Ne.symm hac, by rw [hk2, hfb]⟩
    obtain ⟨u, v, huv, hfk⟩ := hsk k hk
    have hnc1 := hfnc k k₁ hk (Ne.symm ho1) hk1
    have hnc2 := hfnc k k₂ hk (Ne.symm ho2) hk2
    rw [hfk, hfa] at hnc1
    rw [hfk, hfb] at hnc2
    have hnbc : swap u v ≠ swap b c := by
      rw [← hfk, ← hfbc]
      intro h
      have h1 := congrArg (fun σ : Perm (Fin d) => σ o) (hinj h)
      simp only [swap_apply_left] at h1
      rw [swap_apply_of_ne_of_ne ho1 ho2] at h1
      exact hk h1
    rcases share_of_not_commute_swap hnc1 with h | h | h | h
    · exact ⟨v, fun hva => huv (h.trans hva.symm), by rw [hfk, h]⟩
    · rcases share_of_not_commute_swap hnc2 with h' | h' | h' | h'
      · exact absurd (h'.symm.trans h) hab
      · exact absurd (h.symm.trans h') hbc
      · exact ⟨u, h ▸ Ne.symm hab, by rw [hfk, h', swap_comm]⟩
      · exact absurd (by rw [h, h']) hnbc
    · exact ⟨u, fun hua => huv (hua.trans h.symm), by rw [hfk, h, swap_comm]⟩
    · rcases share_of_not_commute_swap hnc2 with h' | h' | h' | h'
      · exact ⟨v, h ▸ Ne.symm hab, by rw [hfk, h']⟩
      · exact absurd (by rw [h', h, swap_comm]) hnbc
      · exact absurd (h'.symm.trans h) hab
      · exact absurd (h.symm.trans h') hbc
  choose! g hg using hstar
  let β : Fin d → Fin d := fun k => if k = o then a else g k
  have hβo : β o = a := by simp [β]
  have hβk : ∀ k, k ≠ o → β k = g k := fun k hk => by simp [β, hk]
  have hβinj : Function.Injective β := by
    intro k k' h
    by_cases hk : k = o
    · by_cases hk' : k' = o
      · rw [hk, hk']
      · rw [hk, hβo, hβk k' hk'] at h
        exact absurd h.symm (hg k' hk').1
    · by_cases hk' : k' = o
      · rw [hk', hβo, hβk k hk] at h
        exact absurd h (hg k hk).1
      · rw [hβk k hk, hβk k' hk'] at h
        have h1 : f (swap o k) = f (swap o k') := by rw [(hg k hk).2, (hg k' hk').2, h]
        exact hev k k' hk (hinj h1)
  set π : Perm (Fin d) := Equiv.ofBijective β (Finite.injective_iff_bijective.mp hβinj) with hπdef
  have hπ : ∀ k, π k = β k := fun k => rfl
  have hagree0 : ∀ k, k ≠ o → f (swap o k) = π * swap o k * π⁻¹ := by
    intro k hk
    rw [← swap_apply_apply, hπ, hπ, hβo, hβk k hk, (hg k hk).2]
  have hagree : ∀ σ : Perm (Fin d), σ.IsSwap → f σ = π * σ * π⁻¹ := by
    rintro σ ⟨x, y, hxy, rfl⟩
    by_cases hx : x = o
    · rw [hx] at hxy ⊢
      exact hagree0 y (Ne.symm hxy)
    by_cases hy : y = o
    · rw [hy, swap_comm]
      exact hagree0 x hx
    have e : swap x y = swap o x * swap o y * swap o x := by
      have h1 := swap_apply_apply (swap o x) o y
      rwa [swap_apply_left, swap_apply_of_ne_of_ne hy (Ne.symm hxy), swap_inv] at h1
    rw [e, map_mul, map_mul, hagree0 x hx, hagree0 y hy]
    group
  refine ⟨π, fun σ => ?_⟩
  have hfeq : f = (MulAut.conj π).toMonoidHom :=
    MonoidHom.eq_of_eqOn_dense Perm.closure_isSwap fun σ hσ => (hagree σ hσ).trans rfl
  rw [hfeq]
  rfl

end CFSG.StandardType

end
