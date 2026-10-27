module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveWeylBRealize
public import Mathlib.Data.ZMod.Basic

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.StandardType

@[expose] def omqSignedAct {n m : ℕ} (π : Equiv.Perm (Fin n)) (s : Fin n → ℤ)
    (ν : Fin n → ZMod m) : Fin n → ZMod m :=
  fun b => ((s (π.symm b) : ℤ) : ZMod m) * ν (π.symm b)

private lemma c2slomqsg_single_add_apply {n m : ℕ} (p q : Fin n) (u v : ZMod m) (x : Fin n) :
    (Pi.single p u + Pi.single q v : Fin n → ZMod m) x =
      (if x = p then u else 0) + (if x = q then v else 0) := by
  rw [Pi.add_apply, Pi.single_apply, Pi.single_apply]

private lemma c2slomqsg_spIsSign_ite {n : ℕ} (p : Fin n) {v : ℤ} (hv : v = 1 ∨ v = -1) :
    SpIsSign (fun d : Fin n => if d = p then v else 1) := by
  intro d
  change (if d = p then v else 1) = 1 ∨ (if d = p then v else 1) = -1
  by_cases h : d = p
  · rw [if_pos h]; exact hv
  · rw [if_neg h]; exact Or.inl rfl

private lemma c2slomqsg_spIsSign_mul {n : ℕ} {s t : Fin n → ℤ} (hs : SpIsSign s)
    (ht : SpIsSign t) : SpIsSign (fun c => s c * t c) := by
  simpa using hs.mul ht (Equiv.refl (Fin n))

theorem omq_exists_signed_perm_two_coord {n : ℕ} (hn : 3 ≤ n) {m : ℕ} {a b a' b' : Fin n}
    (hab : a ≠ b) (hab' : a' ≠ b') {e e' : ℤ} (he : e = 1 ∨ e = -1) (he' : e' = 1 ∨ e' = -1)
    (A B : ZMod m) :
    ∃ (π' : Equiv.Perm (Fin n)) (s' : Fin n → ℤ), SpIsSign s' ∧ ∏ c, s' c = 1 ∧
      omqSignedAct π' s' (Pi.single a A + Pi.single b B) =
        (Pi.single a' ((e : ZMod m) * A) + Pi.single b' ((e' : ZMod m) * B) :
          Fin n → ZMod m) := by
  classical
  obtain ⟨c, hca, hcb⟩ := Fin.exists_ne_and_ne_of_two_lt a b (by omega)
  let π₁ : Equiv.Perm (Fin n) := Equiv.swap a a'
  let b₁ : Fin n := π₁ b
  let π₂ : Equiv.Perm (Fin n) := Equiv.swap b₁ b'
  let π' : Equiv.Perm (Fin n) := π₂ * π₁
  let s' : Fin n → ℤ := fun d =>
    (if d = a then e else 1) * (if d = b then e' else 1) * (if d = c then e * e' else 1)
  have hπ1a : π₁ a = a' := by
    show Equiv.swap a a' a = a'
    exact Equiv.swap_apply_left a a'
  have hb1_ne_a' : b₁ ≠ a' := by
    intro h
    have himg : π₁ b = π₁ a := by
      rw [hπ1a]
      exact h
    exact hab (Equiv.injective π₁ himg).symm
  have hπ2a' : π₂ a' = a' := by
    show Equiv.swap b₁ b' a' = a'
    exact Equiv.swap_apply_of_ne_of_ne (Ne.symm hb1_ne_a') hab'
  have hπ2b1 : π₂ b₁ = b' := by
    show Equiv.swap b₁ b' b₁ = b'
    exact Equiv.swap_apply_left b₁ b'
  have hπ'a : π' a = a' := by
    show π₂ (π₁ a) = a'
    rw [hπ1a, hπ2a']
  have hπ'b : π' b = b' := by
    show π₂ b₁ = b'
    rw [hπ2b1]
  have hsymm_a' : π'.symm a' = a := by
    apply π'.injective
    rw [π'.apply_symm_apply, hπ'a]
  have hsymm_b' : π'.symm b' = b := by
    apply π'.injective
    rw [π'.apply_symm_apply, hπ'b]
  have hs'a : s' a = e := by
    show (if a = a then e else 1) * (if a = b then e' else 1) *
      (if a = c then e * e' else 1) = e
    simp [hab, Ne.symm hca]
  have hs'b : s' b = e' := by
    show (if b = a then e else 1) * (if b = b then e' else 1) *
      (if b = c then e * e' else 1) = e'
    simp [Ne.symm hab, Ne.symm hcb]
  have hs'c : s' c = e * e' := by
    show (if c = a then e else 1) * (if c = b then e' else 1) *
      (if c = c then e * e' else 1) = e * e'
    simp [hca, hcb]
  have hs' : SpIsSign s' := by
    have h1 : SpIsSign (fun d : Fin n => if d = a then e else 1) :=
      c2slomqsg_spIsSign_ite a he
    have h2 : SpIsSign (fun d : Fin n => if d = b then e' else 1) :=
      c2slomqsg_spIsSign_ite b he'
    have h3 : SpIsSign (fun d : Fin n => if d = c then e * e' else 1) :=
      c2slomqsg_spIsSign_ite c
        (by rcases he with h | h <;> rcases he' with h' | h' <;> rw [h, h'] <;> norm_num)
    show SpIsSign (fun d : Fin n => (if d = a then e else 1) * (if d = b then e' else 1) *
      (if d = c then e * e' else 1))
    exact c2slomqsg_spIsSign_mul (c2slomqsg_spIsSign_mul h1 h2) h3
  have hprod : ∏ d, s' d = 1 := by
    show ∏ d, (if d = a then e else 1) * (if d = b then e' else 1) *
      (if d = c then e * e' else 1) = 1
    rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib,
      Fintype.prod_ite_eq' a (fun _ => e), Fintype.prod_ite_eq' b (fun _ => e'),
      Fintype.prod_ite_eq' c (fun _ => e * e')]
    rcases he with h | h <;> rcases he' with h' | h' <;> rw [h, h'] <;> norm_num
  refine ⟨π', s', hs', hprod, ?_⟩
  funext d'
  show ((s' (π'.symm d') : ℤ) : ZMod m) *
      (Pi.single a A + Pi.single b B : Fin n → ZMod m) (π'.symm d') =
    (Pi.single a' ((e : ZMod m) * A) + Pi.single b' ((e' : ZMod m) * B) :
      Fin n → ZMod m) d'
  rw [c2slomqsg_single_add_apply a b A B (π'.symm d'),
    c2slomqsg_single_add_apply a' b' ((e : ZMod m) * A) ((e' : ZMod m) * B) d']
  by_cases hda' : d' = a'
  · rw [hda', hsymm_a', hs'a]
    simp [hab, hab']
  · by_cases hdb' : d' = b'
    · rw [hdb', hsymm_b', hs'b]
      simp [Ne.symm hab, Ne.symm hab']
    · have hna : π'.symm d' ≠ a := by
        intro h
        exact hda' (by rw [← hπ'a, ← h, π'.apply_symm_apply])
      have hnb : π'.symm d' ≠ b := by
        intro h
        exact hdb' (by rw [← hπ'b, ← h, π'.apply_symm_apply])
      rw [if_neg hna, if_neg hnb, if_neg hda', if_neg hdb']
      simp

end CFSG.LocalAnalysis.WeakClosure81
