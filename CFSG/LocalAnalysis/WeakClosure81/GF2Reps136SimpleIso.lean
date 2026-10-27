module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps136SimpleIsoTrans

public section

namespace CFSG.LocalAnalysis.WeakClosure81.GF2Reps136

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open scoped commutatorElement Pointwise Matrix

theorem w1369_ta_iso_case {Q : Type} [CommGroup Q] [Finite Q] (hQ : ∀ x : Q, x ^ 2 = 1)
    {Λ N : Subgroup (MulAut Q)} (hΛN : Λ ≤ N)
    (hnorm : ∀ n ∈ N, ∀ l ∈ Λ, n * l * n⁻¹ ∈ Λ)
    {k : ℕ} (hk : k ≤ 3) {I : Fin k → Subgroup Q} (hstab : ∀ i, StableUnder Λ (I i))
    (hsimple : ∀ i, I i ≠ ⊥ ∧ ∀ J : Subgroup Q, StableUnder Λ J → J ≤ I i → J = ⊥ ∨ J = I i)
    (hspan : ⨆ i, I i = ⊤) (hind : ∀ i, I i ⊓ (⨆ (j : Fin k) (_ : j ≠ i), I j) = ⊥)
    (hend : ∀ i j, i ≠ j → SecIsoOn Λ (I i) ⊥ (I j) ⊥ → ∀ f : Q →* Q,
      (∀ g ∈ Λ, ∀ x, f (g x) = g (f x)) → (∀ x ∈ I i, f x ∈ I i) →
      (∀ j', j' ≠ i → ∀ x ∈ I j', f x = 1) → (∀ x ∈ I i, f x = x) ∨ (∀ x ∈ I i, f x = 1))
    (hiso : ∃ i j, i ≠ j ∧ SecIsoOn Λ (I i) ⊥ (I j) ⊥)
    (hirr : ∀ M : Subgroup Q, StableUnder N M → M = ⊥ ∨ M = ⊤) :
    ∀ S₁ S₂ : Subgroup Q,
      (S₁ ≠ ⊥ ∧ StableUnder Λ S₁ ∧ ∀ J : Subgroup Q, StableUnder Λ J → J ≤ S₁ → J = ⊥ ∨ J = S₁) →
      (S₂ ≠ ⊥ ∧ StableUnder Λ S₂ ∧ ∀ J : Subgroup Q, StableUnder Λ J → J ≤ S₂ → J = ⊥ ∨ J = S₂) →
      ∃ n ∈ N, S₂ = S₁.map n.toMonoidHom := by
  classical
  haveI : Finite (Subgroup Q) :=
    Finite.of_injective (fun H : Subgroup Q => (H : Set Q)) SetLike.coe_injective
  have hIsimple : ∀ i, w1369_ta_IsSimple Λ (I i) :=
    fun i => ⟨(hsimple i).1, hstab i, (hsimple i).2⟩
  have P : w1369_ta_Proj I Λ := w1369_ta_mkProj hstab hspan hind
  have hk' : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 := by omega
  intro S₁ S₂ hS₁ hS₂
  have hS₁' : w1369_ta_IsSimple Λ S₁ := ⟨hS₁.1, hS₁.2.1, hS₁.2.2⟩
  have hS₂' : w1369_ta_IsSimple Λ S₂ := ⟨hS₂.1, hS₂.2.1, hS₂.2.2⟩
  rcases hk' with hk0 | hk1 | hk2 | hk3
  · subst hk0
    obtain ⟨i, -, -, -⟩ := hiso
    exact i.elim0
  · subst hk1
    obtain ⟨i, j, hij, -⟩ := hiso
    exact absurd (Subsingleton.elim i j) hij
  · subst hk2
    obtain ⟨a, b, hab, hsecab⟩ := hiso
    have hisoAll : ∀ i j : Fin 2, i ≠ j → SecIsoOn Λ (I i) ⊥ (I j) ⊥ := by
      intro i j hij
      fin_cases i <;> fin_cases j <;> fin_cases a <;> fin_cases b <;> first
        | exact absurd rfl hij
        | exact absurd rfl hab
        | exact hsecab
        | exact w1369_ta_SecIsoOn_symm hsecab
    have hpart : ∀ i : Fin 2, ∃ j : Fin 2, j ≠ i := by
      intro i
      fin_cases i
      · exact ⟨1, by decide⟩
      · exact ⟨0, by decide⟩
    refine w1369_ta_transitive_on_simple (Ncard := 3) (m := 2) hnorm hpart P hstab hIsimple
      hend hisoAll ?_ ?_ ?_ S₁ S₂ hS₁' hS₂'
    · rw [Nat.card_eq_fintype_card]; decide
    · decide
    · intro S hS
      by_contra hlt
      have hne : (w1369_ta_orb N S).ncard ≠ 0 :=
        Set.ncard_ne_zero_of_mem (w1369_ta_mem_orb_self N S)
      have h1 : (w1369_ta_orb N S).ncard = 1 := by omega
      exact w1369_ta_orb_ne_one (k := 2) (by decide) hstab hIsimple hind hirr hS h1
  · subst hk3
    obtain ⟨a, b, hab, hsecab⟩ := hiso
    have hisoAll := w1369_ta_hisoAll_three hnorm P hstab hIsimple hind hirr hab hsecab
    have hpart : ∀ i : Fin 3, ∃ j : Fin 3, j ≠ i := by
      intro i
      fin_cases i
      · exact ⟨1, by decide⟩
      · exact ⟨0, by decide⟩
      · exact ⟨0, by decide⟩
    refine w1369_ta_transitive_on_simple (Ncard := 7) (m := 4) hnorm hpart P hstab hIsimple
      hend hisoAll ?_ ?_ ?_ S₁ S₂ hS₁' hS₂'
    · rw [Nat.card_eq_fintype_card]; decide
    · decide
    · intro S hS
      by_contra hlt
      have hne : (w1369_ta_orb N S).ncard ≠ 0 :=
        Set.ncard_ne_zero_of_mem (w1369_ta_mem_orb_self N S)
      have hx : (w1369_ta_orb N S).ncard = 1 ∨ (w1369_ta_orb N S).ncard = 2 ∨
          (w1369_ta_orb N S).ncard = 3 := by omega
      rcases hx with h1 | h1 | h1
      · exact w1369_ta_orb_ne_one (k := 3) (by decide) hstab hIsimple hind hirr hS h1
      · exact w1369_ta_orb_ne_two hQ hnorm rfl P hstab hIsimple hisoAll hind hspan hirr hS h1
      · exact w1369_ta_orb_ne_three hQ hnorm P hstab hIsimple hend hisoAll hpart hind hspan
          hirr hS h1

end CFSG.LocalAnalysis.WeakClosure81.GF2Reps136
